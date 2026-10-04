#!/usr/bin/env python3
"""Safety regression tests for source-archive validation; entirely in memory."""
import io
import gzip
import json
import os
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import release

class ArchiveValidationTests(unittest.TestCase):
    def fixture(self, changes=None, extra=None):
        body = b"Review source\n"
        files = [{"path": "README.md", "sha256": release.digest(body),
                  "bytes": len(body), "executable": False}]
        manifest = json.dumps({"schema_version": 1, "source_snapshot": "test",
                               "files": files}).encode()
        members = [("planar-homomorphisms/README.md", body, tarfile.REGTYPE, "", 0o644),
                   ("planar-homomorphisms/RELEASE_MANIFEST.json", manifest, tarfile.REGTYPE, "", 0o644),
                   ("planar-homomorphisms/RELEASE_MANIFEST.sha256",
                    (release.digest(manifest) + "  RELEASE_MANIFEST.json\n").encode(),
                    tarfile.REGTYPE, "", 0o644)]
        if changes:
            members = changes(members)
        if extra:
            members.append(extra)
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode="w:gz") as archive:
            for name, data, kind, link, mode in members:
                entry = tarfile.TarInfo(name)
                entry.type = kind
                entry.linkname = link
                entry.mode = mode
                entry.size = len(data) if kind == tarfile.REGTYPE else 0
                archive.addfile(entry, io.BytesIO(data) if kind == tarfile.REGTYPE else None)
        output.seek(0)
        return output

    def rejects(self, **kwargs):
        with self.assertRaises(RuntimeError):
            release.inspect_archive_fileobj(self.fixture(**kwargs))

    def test_valid_regular_archive(self):
        manifest, payload, modes = release.inspect_archive_fileobj(self.fixture())
        self.assertEqual(len(manifest["files"]), 1)
        self.assertEqual(payload["README.md"], b"Review source\n")
        self.assertEqual(modes["README.md"], 0o644)

    def test_parent_traversal(self):
        self.rejects(extra=("planar-homomorphisms/../../outside", b"x", tarfile.REGTYPE, "", 0o644))

    def test_absolute_path(self):
        self.rejects(extra=("/absolute", b"x", tarfile.REGTYPE, "", 0o644))

    def test_duplicate_member(self):
        self.rejects(extra=("planar-homomorphisms/README.md", b"x", tarfile.REGTYPE, "", 0o644))

    def test_symlink(self):
        self.rejects(extra=("planar-homomorphisms/docs/link", b"", tarfile.SYMTYPE, "../../outside", 0o644))

    def test_hardlink(self):
        self.rejects(extra=("planar-homomorphisms/docs/link", b"", tarfile.LNKTYPE, "../../outside", 0o644))

    def test_cache_inclusion(self):
        self.rejects(extra=("planar-homomorphisms/PlanarHom/.lake/object.olean", b"x", tarfile.REGTYPE, "", 0o644))

    def test_content_mismatch(self):
        self.rejects(changes=lambda m: [(m[0][0], b"wrong", *m[0][2:]), *m[1:]])

    def test_mode_mismatch(self):
        self.rejects(changes=lambda m: [(*m[0][:4], 0o755), *m[1:]])

    def test_missing_member(self):
        self.rejects(changes=lambda m: m[1:])

    def test_unlisted_member(self):
        self.rejects(extra=("planar-homomorphisms/docs/unlisted.md", b"x", tarfile.REGTYPE, "", 0o644))

    def test_special_file(self):
        self.rejects(extra=("planar-homomorphisms/docs/pipe", b"", tarfile.FIFOTYPE, "", 0o644))

    def test_compact_evidence_preserves_retained_contents_and_indexes_omissions(self):
        with tempfile.TemporaryDirectory() as directory:
            run = Path(directory) / "run"
            run.mkdir()
            body = b"checked declaration\n" * 10000
            (run / "audit-scripts.AxiomAudit.log").write_bytes(body)
            (run / "summary.json").write_text('{"status": "PASS"}\n')
            (run / "empty.log").write_bytes(b"")
            (run / "generated.log").write_bytes(b"reproducible detail\n")
            destination = Path(directory) / "evidence"
            release.export_evidence(run, destination)
            self.assertEqual(gzip.decompress(
                (destination / "audit-scripts.AxiomAudit.log.gz").read_bytes()), body)
            self.assertEqual((destination / "summary.json").read_bytes(),
                             (run / "summary.json").read_bytes())
            index = {r["original_path"]: r for r in json.loads(
                (destination / "log-index.json").read_text())}
            for name, entry in index.items():
                self.assertEqual(entry["sha256"], release.sha(run / name))
                self.assertEqual(entry["bytes"], (run / name).stat().st_size)
            self.assertEqual(index["empty.log"]["omitted"], "empty")
            self.assertFalse((destination / "generated.log").exists())

    def test_rebuild_honors_existing_toolchain_and_dependency_root(self):
        with tempfile.TemporaryDirectory() as directory:
            overrides = {"ELAN_HOME": directory + "/installed-elan",
                         "PLGH_DEPENDENCY_ROOT": directory + "/dependencies"}
            with patch.object(release, "ROOT", Path(directory)), patch.dict(os.environ, overrides):
                env = release.local_environment()
            for key, value in overrides.items():
                self.assertEqual(env[key], value)
            self.assertEqual(env["PATH"].split(os.pathsep)[0], str(Path(sys.executable).parent))

if __name__ == "__main__":
    unittest.main()
