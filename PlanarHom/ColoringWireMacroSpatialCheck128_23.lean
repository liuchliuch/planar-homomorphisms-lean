import PlanarHom.ColoringWireMacroSpatialCheck128_22
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem self128_2300 : edgeNode_2494.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2301 : edgeNode_2535.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2302 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2494 edgeNode_2535=true :=
  by decide +kernel

theorem self128_2303 : edgeNode_2536.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2300 self128_2301 apart128_ee_2302

theorem self128_2304 : edgeNode_2577.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2305 : edgeNode_2618.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2306 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2577 edgeNode_2618=true :=
  by decide +kernel

theorem self128_2307 : edgeNode_2619.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2304 self128_2305 apart128_ee_2306

theorem apart128_ee_2308 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2536 edgeNode_2619=true :=
  by decide +kernel

theorem self128_2309 : edgeNode_2620.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2303 self128_2307 apart128_ee_2308

theorem apart128_ee_2310 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2373 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2311 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2454 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2312 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2455 edgeNode_2620=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2310 apart128_ee_2311

theorem self128_2313 : edgeNode_2621.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2299 self128_2309 apart128_ee_2312

theorem apart128_ee_2314 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2046 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2315 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2085 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2316 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2104 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2317 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2113 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2318 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2114 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2319 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2115 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2320 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2116 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2321 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2116 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2322 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2116 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2320 apart128_ee_2321

theorem apart128_ee_2323 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2117 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2319 apart128_ee_2322

theorem apart128_ee_2324 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2118 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2318 apart128_ee_2323

theorem apart128_ee_2325 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2123 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2326 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2124 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2324 apart128_ee_2325

theorem apart128_ee_2327 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2125 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2317 apart128_ee_2326

theorem apart128_ee_2328 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2126 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2316 apart128_ee_2327

theorem apart128_ee_2329 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2127 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2315 apart128_ee_2328

theorem apart128_ee_2330 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2128 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2314 apart128_ee_2329

theorem apart128_ee_2331 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2167 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2332 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2170 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2333 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2171 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2334 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2172 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2335 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2173 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2336 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2173 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2337 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2173 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2335 apart128_ee_2336

theorem apart128_ee_2338 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2174 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2334 apart128_ee_2337

theorem apart128_ee_2339 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2175 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2333 apart128_ee_2338

theorem apart128_ee_2340 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2176 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2332 apart128_ee_2339

theorem apart128_ee_2341 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2177 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2342 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2177 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2343 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2177 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2341 apart128_ee_2342

theorem apart128_ee_2344 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2178 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2345 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2179 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2343 apart128_ee_2344

theorem apart128_ee_2346 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2180 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2347 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2181 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2348 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2181 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2349 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2181 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2347 apart128_ee_2348

theorem apart128_ee_2350 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2182 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2351 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2182 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2352 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2182 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2350 apart128_ee_2351

theorem apart128_ee_2353 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2183 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2349 apart128_ee_2352

theorem apart128_ee_2354 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2184 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2346 apart128_ee_2353

theorem apart128_ee_2355 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2185 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2345 apart128_ee_2354

theorem apart128_ee_2356 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2186 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2340 apart128_ee_2355

theorem apart128_ee_2357 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2187 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2358 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2187 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2359 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2187 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2357 apart128_ee_2358

theorem apart128_ee_2360 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2188 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2361 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2188 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2362 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2188 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2360 apart128_ee_2361

theorem apart128_ee_2363 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2189 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2359 apart128_ee_2362

theorem apart128_ee_2364 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2190 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2365 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2190 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2366 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2190 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2364 apart128_ee_2365

theorem apart128_ee_2367 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2191 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2368 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2191 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2369 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2191 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2367 apart128_ee_2368

theorem apart128_ee_2370 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2192 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2371 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2192 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2372 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2192 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2370 apart128_ee_2371

theorem apart128_ee_2373 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2193 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2369 apart128_ee_2372

theorem apart128_ee_2374 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2194 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2366 apart128_ee_2373

theorem apart128_ee_2375 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2195 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2363 apart128_ee_2374

theorem apart128_ee_2376 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2196 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2377 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2196 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2378 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2196 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2376 apart128_ee_2377

theorem apart128_ee_2379 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2197 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2380 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2197 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2381 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2197 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2379 apart128_ee_2380

theorem apart128_ee_2382 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2198 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2383 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2198 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2384 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2198 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2382 apart128_ee_2383

theorem apart128_ee_2385 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2199 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2381 apart128_ee_2384

theorem apart128_ee_2386 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2200 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2378 apart128_ee_2385

theorem apart128_ee_2387 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2201 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2388 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2201 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2389 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2201 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2387 apart128_ee_2388

theorem apart128_ee_2390 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2202 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2391 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2202 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2392 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2202 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2390 apart128_ee_2391

theorem apart128_ee_2393 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2203 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2394 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2203 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2395 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2203 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2393 apart128_ee_2394

theorem apart128_ee_2396 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2204 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2392 apart128_ee_2395

theorem apart128_ee_2397 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2205 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2389 apart128_ee_2396

theorem apart128_ee_2398 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2206 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2386 apart128_ee_2397

theorem apart128_ee_2399 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2207 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2375 apart128_ee_2398

end PlanarHom.ColoringWireMacroCoordinates
