import PlanarHom.ColoringCrossMacroSpatialCheck128_192
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ev_19300 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19301 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19302 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19303 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19301 apart128_ev_19302

theorem apart128_ev_19304 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19305 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19303 apart128_ev_19304

theorem apart128_ev_19306 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19300 apart128_ev_19305

theorem apart128_ev_19307 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19308 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1906 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19306 apart128_ev_19307

theorem apart128_ev_19309 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19310 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19311 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19312 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19310 apart128_ev_19311

theorem apart128_ev_19313 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19314 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19312 apart128_ev_19313

theorem apart128_ev_19315 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19309 apart128_ev_19314

theorem apart128_ev_19316 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19317 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1907 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19315 apart128_ev_19316

theorem apart128_ev_19318 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1908 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19308 apart128_ev_19317

theorem apart128_ev_19319 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19320 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19321 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19322 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19320 apart128_ev_19321

theorem apart128_ev_19323 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_1106=true :=
  by decide +kernel

theorem apart128_ev_19324 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_1265=true :=
  by decide +kernel

theorem apart128_ev_19325 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_1266=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19323 apart128_ev_19324

theorem apart128_ev_19326 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19322 apart128_ev_19325

theorem apart128_ev_19327 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19319 apart128_ev_19326

theorem apart128_ev_19328 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19329 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1909 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19327 apart128_ev_19328

theorem apart128_ev_19330 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19331 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19332 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19333 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19331 apart128_ev_19332

theorem apart128_ev_19334 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_1106=true :=
  by decide +kernel

theorem apart128_ev_19335 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_1265=true :=
  by decide +kernel

theorem apart128_ev_19336 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_1266=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19334 apart128_ev_19335

theorem apart128_ev_19337 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19333 apart128_ev_19336

theorem apart128_ev_19338 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19330 apart128_ev_19337

theorem apart128_ev_19339 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19340 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1910 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19338 apart128_ev_19339

theorem apart128_ev_19341 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1911 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19329 apart128_ev_19340

theorem apart128_ev_19342 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1912 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19318 apart128_ev_19341

theorem apart128_ev_19343 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1913 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19299 apart128_ev_19342

theorem apart128_ev_19344 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1914 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19270 apart128_ev_19343

theorem apart128_ev_19345 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1915 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19211 apart128_ev_19344

theorem apart128_ev_19346 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19347 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19348 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19349 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19347 apart128_ev_19348

theorem apart128_ev_19350 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19351 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19349 apart128_ev_19350

theorem apart128_ev_19352 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19346 apart128_ev_19351

theorem apart128_ev_19353 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19354 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1916 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19352 apart128_ev_19353

theorem apart128_ev_19355 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19356 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19357 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19358 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19356 apart128_ev_19357

theorem apart128_ev_19359 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19360 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19358 apart128_ev_19359

theorem apart128_ev_19361 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19355 apart128_ev_19360

theorem apart128_ev_19362 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19363 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1917 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19361 apart128_ev_19362

theorem apart128_ev_19364 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19365 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19366 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19367 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19365 apart128_ev_19366

theorem apart128_ev_19368 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19369 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19367 apart128_ev_19368

theorem apart128_ev_19370 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19364 apart128_ev_19369

theorem apart128_ev_19371 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19372 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1918 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19370 apart128_ev_19371

theorem apart128_ev_19373 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1919 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19363 apart128_ev_19372

theorem apart128_ev_19374 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1920 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_19354 apart128_ev_19373

theorem apart128_ev_19375 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19376 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19377 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19378 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19376 apart128_ev_19377

theorem apart128_ev_19379 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19380 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19378 apart128_ev_19379

theorem apart128_ev_19381 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19375 apart128_ev_19380

theorem apart128_ev_19382 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19383 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1921 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19381 apart128_ev_19382

theorem apart128_ev_19384 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19385 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19386 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19387 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19385 apart128_ev_19386

theorem apart128_ev_19388 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19389 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19387 apart128_ev_19388

theorem apart128_ev_19390 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19384 apart128_ev_19389

theorem apart128_ev_19391 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_19392 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1922 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19390 apart128_ev_19391

theorem apart128_ev_19393 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_632=true :=
  by decide +kernel

theorem apart128_ev_19394 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_789=true :=
  by decide +kernel

theorem apart128_ev_19395 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_948=true :=
  by decide +kernel

theorem apart128_ev_19396 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_949=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19394 apart128_ev_19395

theorem apart128_ev_19397 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_1266=true :=
  by decide +kernel

theorem apart128_ev_19398 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_1267=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19396 apart128_ev_19397

theorem apart128_ev_19399 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1923 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_19393 apart128_ev_19398

end PlanarHom.ColoringCrossMacroCoordinates
