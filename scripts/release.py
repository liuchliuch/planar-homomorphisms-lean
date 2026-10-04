#!/usr/bin/env python3
"""Stage, rebuild, and publish a source archive; never publish to a network."""
from pathlib import Path, PurePosixPath
import argparse, datetime, gzip, hashlib, io, json, os, shutil, subprocess, sys, tarfile

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE_ROOT = "planar-homomorphisms"
ROOT_FILES = {"PlanarHom.lean", "README.md", "lakefile.toml", "lake-manifest.json",
              "lean-toolchain", "SOURCE_PROVENANCE.json", ".gitignore", "CITATION.cff"}
SOURCE_DIRS = {"PlanarHom", "Audit", "scripts", "docs", "paper", "verification", ".github"}
BAD_SUFFIXES = {".olean", ".ilean", ".o", ".so", ".dylib", ".pyc"}
MANIFEST = "RELEASE_MANIFEST.json"
CHECKSUM = "RELEASE_MANIFEST.sha256"

def digest(data):
    return hashlib.sha256(data).hexdigest()

def sha(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")

def relative_name(name):
    path = PurePosixPath(name)
    require(name == str(path) and not path.is_absolute() and
            bool(path.parts) and ".." not in path.parts and "\\" not in name and
            "\0" not in name, f"Unsafe path: {name!r}")
    return path

def regular(root, name):
    relative_name(name)
    path = root / name
    require(not path.is_symlink(), f"Symlink: {name}")
    for parent in path.parents:
        if parent == root:
            break
        require(not parent.is_symlink(), f"Symlink parent: {name}")
    require(path.is_file(), f"Missing regular file: {name}")
    return path

def portable_name(name):
    p = relative_name(name)
    return (name in ROOT_FILES or p.parts[0] in SOURCE_DIRS) and not (
        any(x in {".lake", ".build", ".cache", ".tools", ".tmp", "__pycache__", ".git"}
            for x in p.parts) or p.suffix in BAD_SUFFIXES or p.name == ".DS_Store")

def inventory(root):
    paths = [root / name for name in ROOT_FILES if (root / name).exists()]
    for name in sorted(SOURCE_DIRS):
        base = root / name
        if not base.exists():
            continue
        require(not base.is_symlink(), f"Symlink source directory: {name}")
        for directory, dirs, files in os.walk(base, followlinks=False):
            for child in dirs:
                require(not (Path(directory) / child).is_symlink(),
                        f"Symlink directory: {directory}/{child}")
            for child in files:
                paths.append(Path(directory) / child)
    records = []
    for path in sorted(paths):
        name = path.relative_to(root).as_posix()
        require(portable_name(name), f"Unexpected file in source inventory: {name}")
        path = regular(root, name)
        records.append({"path": name, "sha256": sha(path), "bytes": path.stat().st_size,
                        "executable": bool(path.stat().st_mode & 0o111)})
    return records

def snapshot(root):
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.check_output([sys.executable, "scripts/snapshot.py"],
                                     cwd=root, env=env)
    return digest(result), result.decode()

def check_source(root):
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    subprocess.run([sys.executable, "scripts/check_provenance.py"], cwd=root,
                   env=env, check=True)
    require(sha(regular(root, "paper/paper.pdf")) ==
            "366b92c0dfafc076a43751b04cae1296562d3b87ec97a9b27d8a25085dc407f5",
            "Paper checksum mismatch")

def package(root, destination, status):
    check_source(root)
    require(not destination.exists(), f"Refusing to overwrite: {destination}")
    files = inventory(root)
    sid, _ = snapshot(root)
    manifest = {"schema_version": 1, "status": status, "source_snapshot": sid,
                "files": files,
                "note": "Source snapshot covers all Lean, audit, verifier, and pinned configuration inputs."}
    data = (json.dumps(manifest, indent=2, ensure_ascii=False) + "\n").encode()
    checksum = (digest(data) + "  " + MANIFEST + "\n").encode()
    destination.parent.mkdir(parents=True, exist_ok=True)
    require(shutil.disk_usage(destination.parent).free >
            sum(item["bytes"] for item in files) + 64 * 1024**2, "Insufficient disk space")
    with destination.open("xb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as archive:
                for item in files:
                    path = regular(root, item["path"])
                    entry = tarfile.TarInfo(ARCHIVE_ROOT + "/" + item["path"])
                    entry.size = item["bytes"]
                    entry.mode = 0o755 if item["executable"] else 0o644
                    with path.open("rb") as handle:
                        archive.addfile(entry, handle)
                for name, body in [(MANIFEST, data), (CHECKSUM, checksum)]:
                    entry = tarfile.TarInfo(ARCHIVE_ROOT + "/" + name)
                    entry.size = len(body)
                    entry.mode = 0o644
                    archive.addfile(entry, io.BytesIO(body))
    require(inventory(root) == files and snapshot(root)[0] == sid,
            "Source changed during packaging; archive is not verified")
    return manifest, data, checksum

def inspect_archive(path):
    require(path.is_file() and not path.is_symlink(), "Archive must be a regular file")
    with path.open("rb") as handle:
        return inspect_archive_fileobj(handle)

def inspect_archive_fileobj(handle):
    """Validate the complete member inventory before any extraction writes."""
    payload = {}
    modes = {}
    with tarfile.open(fileobj=handle, mode="r:gz") as archive:
        members = archive.getmembers()
        require(len(members) <= 30000, "Excessive archive member count")
        require(sum(m.size for m in members) <= 2 * 1024**3, "Excessive expanded size")
        for member in members:
            p = relative_name(member.name)
            require(member.isfile() and not member.issym() and not member.islnk(),
                    f"Nonregular archive member: {member.name}")
            require(len(p.parts) >= 2 and p.parts[0] == ARCHIVE_ROOT, "Wrong archive root")
            name = PurePosixPath(*p.parts[1:]).as_posix()
            require(name not in payload, f"Duplicate member: {name}")
            require(name in {MANIFEST, CHECKSUM} or portable_name(name),
                    f"Unapproved archive content: {name}")
            require(member.mode in {0o644, 0o755}, f"Unexpected mode: {member.name}")
            handle = archive.extractfile(member)
            require(handle is not None, f"Missing member data: {name}")
            payload[name] = handle.read()
            modes[name] = member.mode
    require(MANIFEST in payload and CHECKSUM in payload, "Missing manifest")
    require(payload[CHECKSUM].decode().strip() ==
            digest(payload[MANIFEST]) + "  " + MANIFEST, "Manifest checksum mismatch")
    manifest = json.loads(payload[MANIFEST])
    files = manifest["files"]
    require(len({f["path"] for f in files}) == len(files), "Duplicate manifest record")
    require(set(payload) == {f["path"] for f in files} | {MANIFEST, CHECKSUM},
            "Manifest/member inventory mismatch")
    for f in files:
        name = f["path"]
        require(sha_bytes_match(payload[name], f), f"Hash/size mismatch: {name}")
        require(modes[name] == (0o755 if f["executable"] else 0o644),
                f"Executable-mode mismatch: {name}")
    return manifest, payload, modes

def sha_bytes_match(body, record):
    return digest(body) == record["sha256"] and len(body) == record["bytes"]

def safe_extract(path, destination):
    manifest, payload, modes = inspect_archive(path)
    require(not destination.exists() and not destination.is_symlink(),
            f"Refusing existing extraction destination: {destination}")
    require(destination.resolve().is_relative_to(ROOT / ".tmp"),
            "Extraction must stay in the project's .tmp")
    for parent in destination.parents:
        require(not parent.is_symlink(), f"Symlink extraction parent: {parent}")
        if parent == ROOT:
            break
    destination.mkdir(parents=True)
    root = destination / ARCHIVE_ROOT
    for name, body in payload.items():
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as handle:
            handle.write(body)
        target.chmod(modes[name])
    require(inventory(root) == manifest["files"], "Extracted/source inventory mismatch")
    require(snapshot(root)[0] == manifest["source_snapshot"], "Extracted snapshot mismatch")
    return root, manifest

def local_environment():
    env = os.environ.copy()
    tool = ROOT / ".tools/elan/toolchains/leanprover--lean4---v4.24.0/bin"
    # verify.sh invokes python3; do not let Apple's Git directory select its
    # older bundled Python instead of the interpreter running this release.
    additions = [str(Path(sys.executable).parent)]
    git = Path("/Library/Developer/CommandLineTools/usr/bin/git")
    if sys.platform == "darwin" and git.is_file():
        additions.append(str(git.parent))
    if (tool / "lean").is_file():
        additions.append(str(tool))
    env["PATH"] = os.pathsep.join(additions + [env.get("PATH", "")])
    if (tool / "lean").is_file():
        env["ELAN_HOME"] = str(ROOT / ".tools/elan")
    env["TMPDIR"] = str(ROOT / ".tmp")
    env["XDG_CACHE_HOME"] = str(ROOT / ".cache")
    env["MATHLIB_CACHE_DIR"] = str(ROOT / ".cache/mathlib")
    env.setdefault("PLGH_DEPENDENCY_ROOT", str(ROOT / ".lake/packages"))
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env

def rebuild(path, jobs):
    archive_sha = sha(path)
    extraction, manifest = safe_extract(path, ROOT / ".tmp/archive-rebuild" / archive_sha)
    require(inventory(ROOT) == manifest["files"], "Candidate differs from current portable tree")
    sid = manifest["source_snapshot"]
    label = "archive-" + archive_sha[:16]
    env = local_environment()
    env["PLGH_JOBS"] = str(jobs)
    env.pop("PLGH_RESUME_FROM", None)
    evidence = ROOT / ".audit" / label
    evidence.mkdir(parents=True, exist_ok=False)
    command = ["bash", "scripts/verify.sh", label]
    receipt = {"candidate_archive": str(path), "candidate_sha256": archive_sha,
               "source_snapshot": sid, "extraction": str(extraction),
               "command": command, "cwd": str(extraction), "started_utc": now(),
               "jobs": jobs, "fresh_project_objects": True,
               "dependency_root": env["PLGH_DEPENDENCY_ROOT"]}
    print("Rebuilding extracted source:", extraction, flush=True)
    with (evidence / "console.log").open("w") as log:
        process = subprocess.Popen(command, cwd=extraction, env=env,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end="", flush=True)
        code = process.wait()
    receipt.update(exit_code=code, finished_utc=now())
    if code == 0:
        success = json.loads((extraction / "logs/latest-success.json").read_text())
        require(success["status"] == "PASS" and success["exit"] == 0 and
                success["snapshot"] == sid and
                success["source_only_project_recompile"] and
                not success["baseline_project_artifacts_reused"] and
                success.get("contract_checks") == 3 and success.get("paper_items_checked") == 58 and
                success.get("reviewed_signature_contracts") == 100 and success.get("reviewed_contract_items") == 58,
                "Full verification gates are incomplete")
        require(snapshot(ROOT)[0] == sid and snapshot(extraction)[0] == sid,
                "Source changed during archive rebuild")
        require(inventory(ROOT) == manifest["files"], "Portable tree changed during archive rebuild")
        receipt.update(success=success, run=str(extraction / success["run"]),
                       exact_portable_tree_match=True)
    write_json(evidence / "receipt.json", receipt)
    print("Archive rebuild receipt:", evidence / "receipt.json", flush=True)
    require(code == 0, f"Archive rebuild failed with exit {code}")
    return evidence / "receipt.json"

def export_evidence(run, destination):
    require(not destination.exists(), f"Evidence already exists: {destination}")
    destination.mkdir(parents=True)
    retained = {
        "summary.json", "target-results.json", "source-snapshot.sha256",
        "dependency-pins.json", "toolchain.txt", "regression-audit-results.json",
        "contract-Audit.Check.log", "contract-Audit.ReviewedCheck.log",
        "contract-Audit.Inventory.log", "audit-scripts.AxiomAudit.log",
        "audit-scripts.CompletedStatementScopeAudit.log", "archive-safety-tests.log",
        "accepted-source-guard.log", "source-guards.log",
    }
    index = []
    for source in sorted(run.rglob("*")):
        if not source.is_file() or "build" in source.relative_to(run).parts:
            continue
        name = source.relative_to(run).as_posix()
        require(not source.is_symlink(), f"Symlink evidence: {source}")
        entry = {"original_path": name, "sha256": sha(source), "bytes": source.stat().st_size}
        if name in retained:
            compressed = source.suffix == ".log" and source.stat().st_size > 128 * 1024
            portable_name = name + ".gz" if compressed else name
            target = destination / portable_name
            target.parent.mkdir(parents=True, exist_ok=True)
            if compressed:
                target.write_bytes(gzip.compress(source.read_bytes(), mtime=0))
            else:
                shutil.copyfile(source, target)
            entry["portable_path"] = portable_name
            if compressed:
                entry["encoding"] = "gzip"
        else:
            entry["omitted"] = "empty" if not source.stat().st_size else "reproducible run detail"
        index.append(entry)
    write_json(destination / "log-index.json", index)

def publish(receipt_path):
    receipt = json.loads(receipt_path.read_text())
    require(receipt["exit_code"] == 0 and receipt.get("exact_portable_tree_match"),
            "No successful archive rebuild")
    sid = receipt["source_snapshot"]
    require(snapshot(ROOT)[0] == sid, "Current source differs from rebuilt archive")
    run = Path(receipt["run"])
    require(run.resolve().is_relative_to(ROOT / ".tmp"), "Run must be in local extraction")
    summary = json.loads((run / "summary.json").read_text())
    require(summary["status"] == "PASS" and summary["snapshot"] == sid, "Invalid run summary")
    require((run / "source-snapshot.sha256").read_text() == snapshot(ROOT)[1],
            "Rebuilt source file hashes differ")
    if (ROOT / "verification").exists():
        backup = ROOT / ".audit" / ("previous-evidence-" + datetime.datetime.now(
            datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ"))
        backup.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(ROOT / "verification"), str(backup))
    export_evidence(run, ROOT / "verification/final")
    write_json(ROOT / "verification/archive-rebuild.json", receipt)
    report = (
        "# Verification results\n\n"
        "The final source, audit interface, and verifier were freshly compiled from an extracted "
        "candidate source archive. The delivered archive adds these evidence files and this report; "
        "its complete source/tool/configuration snapshot is identical to that fresh build. "
        "A final safe extraction checks all delivered files against the source tree.\n\n"
        f"- Source snapshot: `{sid}`\n"
        f"- Lean: `{summary['toolchain']}`\n"
        f"- Full verifier exit: `{receipt['exit_code']}`\n"
        f"- Production modules: {summary['project_modules']} plus the aggregate\n"
        f"- Script regressions and isolated audits: {summary['script_regression_suites']} each\n"
        f"- Project declarations audited: {summary['project_declarations']}\n"
        f"- Project theorem declarations: {summary['project_theorem_declarations']}\n"
        f"- Independent proposition contracts: {summary['contract_checks']}\n"
        f"- Reviewed full-type contracts: {summary['reviewed_signature_contracts']} across {summary['reviewed_contract_items']} paper items\n"
        f"- Numbered paper items inventoried: {summary['paper_items_checked']}\n"
        "- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`\n"
        "- Official Linux comparator: not run; no equivalent sandbox claim\n\n"
        "See `verification/final/` for per-target commands, exit codes, source/object hashes, "
        "statement checks, origin audits, and unchanged-source guards. Large retained logs "
        "are gzip-compressed; `log-index.json` records the uncompressed size and hash of "
        "every run file and identifies omitted reproducible diagnostics and generated audit inputs. "
        "Full raw logs are produced locally under `logs/runs/` when the verifier runs. "
        "`verification/archive-rebuild.json` "
        "records the actual extraction, command, timings, and dependency location. "
        "Absolute execution paths are historical evidence, not required build inputs.\n\n"
        "This kernel/dependency result is separate from the statement and model review in "
        "[PAPER_AUDIT.md](PAPER_AUDIT.md). It is not an independent kernel implementation "
        "or a manual review of every proof line.\n")
    (ROOT / "docs/VERIFICATION.md").write_text(report)
    require(snapshot(ROOT)[0] == sid, "Evidence publication changed verified sources")
    destination = ROOT / ("planar-homomorphisms-reviewed-" + sid[:16] + ".tar.gz")
    manifest, data, checksum = package(ROOT, destination, "SOURCE_ARCHIVE_REBUILD_VERIFIED")
    final_sha = sha(destination)
    extracted, checked = safe_extract(destination, ROOT / ".tmp/final-inspection" / final_sha)
    require(checked == manifest and inventory(ROOT) == checked["files"],
            "Final archive/source mismatch")
    require(snapshot(extracted)[0] == sid, "Final archive differs from rebuilt sources")
    (ROOT / MANIFEST).write_bytes(data)
    (ROOT / CHECKSUM).write_bytes(checksum)
    destination.with_name(destination.name + ".sha256").write_text(
        final_sha + "  " + destination.name + "\n")
    final_receipt = {
        "archive": str(destination), "sha256": final_sha,
        "source_snapshot": sid, "regular_members": len(manifest["files"]) + 2,
        "safe_extraction": True, "exact_portable_source_match": True,
        "same_source_tools_and_pins_as_fresh_archive_build": True,
        "fresh_archive_build_exit": receipt["exit_code"],
        "fresh_build_receipt": "verification/archive-rebuild.json",
        "final_extraction": str(extracted), "checked_utc": now()}
    write_json(destination.with_name(destination.name + ".verification.json"), final_receipt)
    print(json.dumps(final_receipt, indent=2))
    return destination

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    stage = sub.add_parser("stage")
    stage.add_argument("--output", type=Path)
    verify = sub.add_parser("rebuild")
    verify.add_argument("archive", type=Path)
    verify.add_argument("--jobs", type=int, default=4)
    final = sub.add_parser("publish")
    final.add_argument("receipt", type=Path)
    inspect = sub.add_parser("inspect")
    inspect.add_argument("archive", type=Path)
    args = parser.parse_args()
    if args.action == "stage":
        sid, _ = snapshot(ROOT)
        path = args.output or ROOT / ".tmp" / ("candidate-" + sid[:16] + ".tar.gz")
        require(path.absolute().is_relative_to(ROOT), "Candidate must remain inside the project")
        manifest, _, _ = package(ROOT, path, "CANDIDATE_NOT_YET_REBUILT")
        print(path)
        print("source_snapshot", manifest["source_snapshot"])
    elif args.action == "rebuild":
        require(1 <= args.jobs <= 16, "Jobs must be between 1 and 16")
        rebuild(args.archive.absolute(), args.jobs)
    elif args.action == "publish":
        publish(args.receipt.absolute())
    else:
        manifest, _, _ = inspect_archive(args.archive.absolute())
        print(json.dumps({"archive_sha256": sha(args.archive), "safe": True,
                          "files": len(manifest["files"]),
                          "source_snapshot": manifest["source_snapshot"]}, indent=2))

if __name__ == "__main__":
    main()
