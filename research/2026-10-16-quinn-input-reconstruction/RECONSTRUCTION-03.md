# Reconstructing Quinn's 11,225 viewpoints: recovered inputs and exact gaps

2026-10-16 UTC. Contributor/publisher: Codex, continuation integration. **Status: historical source candidate recovered and checked; exact processed-input reconstruction remains underdetermined.** Additive continuation of [the impact audit](../2026-10-16-issue-impact-audit/ISSUE-IMPACT-01.md); no change to that audit or the citation review.

**Result:** A small, official WSDOT 2019 traffic-segment geodatabase is publicly downloadable and has been preserved here. Its geometry-length total is **11,362.1784796809 km**, consistent with Quinn's reported approximately 11,362 km. Historical USGS one-arc-second DEM versions and their provenance metadata are also accessible. These are concrete reconstruction inputs, not merely current substitutes. Neither source establishes the exact 11,225 point coordinates, the DEM grid, or whether any command failed in the original analysis.

## 1. What must be reconstructed

[Quinn, Methods §3 and Data availability](https://gh.copernicus.org/articles/77/165/2022/) describes USGS one-arc-second elevation tiles, projection to UTM zone 10N, mosaic and clipping to an official Washington boundary including water; 2019 WSDOT traffic polylines; joining by route number; sampling every kilometre; removing known tunnel points; and spatially joining traffic counts. It names no item IDs, tile editions or point archive. The 28 April 2022 website access date is not necessarily the data-download or processing date; the manuscript was initially received 28 July 2021.

The preserved supplementary script specifically expects `points_to_analyze.csv` with `X`, `Y`, `TARGET_FID`, `AADT`, and `clipped_nad83_1arcsec.tif`. These exact processed files are the shortest route to faithful reproduction; the supplement does not contain them. The DEM filename suggests NAD83, but does not establish its complete CRS definition, grid or resampling settings.

## 2. Actual WSDOT historical source

- **Dataset:** Traffic Sections 2019, Washington State Department of Transportation. [Official ZIP](https://data.wsdot.wa.gov/geospatial/DOT_TDO/TrafficGeoportal/2019_TrafficSections.zip), discovered through the [item's metadata XML](https://www.arcgis.com/sharing/rest/content/items/f736c9dfdb0c49909e9caccd5beb5410/info/metadata/metadata.xml). The local original is [evidence/2019_TrafficSections.zip](evidence/2019_TrafficSections.zip).
- **Exact present item:** [`f736c9dfdb0c49909e9caccd5beb5410`](https://www.arcgis.com/home/item.html?id=f736c9dfdb0c49909e9caccd5beb5410), authoritative WSDOT owner. It resolves to [HistoricTrafficData_3/FeatureServer/7](https://services.arcgis.com/IYrj3otxNjPsrTRD/ArcGIS/rest/services/HistoricTrafficData_3/FeatureServer/7). Layer 6 is traffic-count locations; it is **not** the polyline input described by Quinn.
- **File provenance:** ZIP 1,418,213 bytes; SHA-256 `f16747ac4aa85cd7b75cfceb6c352ae30c37213ded1518a37284a05f72a7e642`. Embedded FGDC metadata: publication 2020-06-05, temporal coverage 2019-01-01 to 2019-12-31, processing 2020-05-14. The archive's main feature-table entries bear June 2020 timestamps; metadata/catalog entries were changed in October 2024. HTTP Last-Modified is 2024-10-17. ZIP timestamps are evidence about packaging, not cryptographic historical certification.
- **Lineage:** metadata describes consolidating contiguous equal-AADT segments and splitting where directionality changes, then placing events on the 2019 increasing 1:24K linear referencing system, using decreasing routes for segments without increasing lanes, and merging those results.

The portal item was created **2022-02-03**, after initial manuscript submission, and modified 2025-10-07. Its parent service was modified in 2026; the layer's edit timestamp is 2026-09-04. The service reports `hasVersionedData=false` and `hasStaticData=false`. Thus the year label identifies historical subject matter, not an immutable download from 2020/2021. The available ZIP plus matching length is a strong candidate, **not proven byte-identical to Quinn's original**. A bounded Wayback index query for this exact portal item found 2024–2026 page captures, not a pre-submission dataset copy.

### Read-only checks actually executed

`ogrinfo` opened the recovered FileGDB through OpenFileGDB. No road resampling, statewide raster processing or original script execution was performed.

| Check | Result |
|---|---|
| Layer / geometry | `TrafficSections2019`; MultiLineString |
| Segment count | 4,913, also matching the live layer count |
| Source CRS | NAD83(HARN) / Washington South (US survey feet), EPSG:2927 |
| Extent from embedded metadata | longitude −124.674393 to −116.861321; latitude 45.504794 to 49.042512 |
| Distinct keys | 188 `StateRouteNumber`; 251 `RouteIdentifier` |
| AADT | integer; zero null values; range 60–257,000 |
| Length diagnostic | sum `SHAPE_Length` × 0.304800609601219 / 1000 = 11,362.1784796809 km |
| Route types | blank 4,714; AR 26; CO 64; HD 3; HI 2; RL 9; SP 95 |

Other fields include `LRSDate`, `RelatedRouteQualifier`, begin/end accumulated route miles, `Location`, `GlobalID`. The live service reprojects geometry to EPSG:3857, whereas the downloadable FileGDB retains EPSG:2927. Do not measure a 1 km sampling interval directly in Web Mercator or confuse feet with metres. The stored-length check supports source identification; it is not a geodesic survey or proof of a historical byte match.

The item advertises planning-use terms and disclaimers, **not CC0**. Preserve WSDOT attribution and consult the verbatim `licenseInfo` in [the item record](evidence/wsdot-2019-item.json) and `useconst` in the ZIP's FGDC XML. The separate [2019 state-route 1:24K item](https://www.arcgis.com/home/item.html?id=7d0bc7eb797949e0a6d13726f21850bb) includes additional route-system classes; its reported size is 338,927,616 bytes and it was not downloaded. It is not silently substituted for the traffic dataset.

## 3. Actual historical USGS elevation access

The public [TNM dataset catalog](https://tnmaccess.nationalmap.gov/api/v1/datasets) identifies the collection `National Elevation Dataset (NED) 1 arc-second`. Two metadata-only product requests for bounding box `-124.8,45.5,-116.9,49.05`, `max=100`, offsets 0 and 100 returned **178 distinct historical records across 45 tile names**. The box intentionally overcovers Washington; this is not a final state-intersection inventory. Both responses, including download URLs and dates, are preserved under `evidence/tnm-wa-products*.json`.

For example, `n48w123` has archived editions labelled 20200107, 20210615, 20220505, 20230307, 20230608 and 20240327. The [public object listing](https://prd-tnm.s3.amazonaws.com/?list-type=2&prefix=StagedProducts/Elevation/1/TIFF/historical/n48w123/&max-keys=100) verifies their existence and actual sizes. The 20200107 raster is **50,609,628 bytes**, and the 20210615 raster is **51,234,761 bytes**. Neither raster was downloaded.

Small authentic historical metadata were downloaded and preserved: [20200107 XML](evidence/USGS_1_n48w123_20200107.xml), 11,557 bytes, and [spatial-provenance GeoPackage](evidence/USGS_1_n48w123_20200107.gpkg), 565,248 bytes. The latter is **92 source-provenance polygons**, EPSG:4269, not elevation pixels. XML gives publication 2020-01-07, source temporal extent 2017-09-14 to 2019-04-25, NAD83 horizontal reference, NAVD88 elevations in metres and 0.00027777778-degree spacing. USGS describes 3DEP products as freely available without use restrictions; the XML also retains its attribution/modification and accuracy conditions. [USGS product documentation](https://www.usgs.gov/3d-elevation-program/about-3dep-products-services).

**Size/date validation matters:** TNM's older `n46w117_20190917` record says `sizeInBytes=55122`; a HEAD request to its exact TIFF returned **56,447,050 bytes**. The S3 upload date is December 2022 despite the older edition label. Do not interpret old catalog sizes as small rasters, sum them as a reliable download budget, or infer original availability solely from upload/filename dates. One `n48w123_20210615` catalog record has publication date November 2021 despite its filename date. ScienceBase item metadata fetch returned 403, but the S3 historical XML and listings were available.

A defensible reconstruction needs an explicit per-tile version manifest tied to the original acquisition period. “Use today's 1 arc-second layer” would silently change the terrain. The precise manifest cannot be selected from this paper alone.

## 4. Search for processed inputs before reconstruction

The article's data statement points to source agencies, not a processed-data repository. Its supplement was already inspected and contains the script, not the named CSV or DEM. This run checked public ArcGIS search for cumulative viewshed/author, DataCite searches for the exact title, the article DOI as a related identifier, and the author name; it also inspected the article-linked public ORCID record and works. **No matching processed-point or raster deposit was located.** The DOI/title DataCite queries each returned zero; author-name matches included unrelated people and other works and were not accepted as deposits. ORCID linked the paper but provided no researcher URL or relevant dataset. This is a bounded search, not proof that no unindexed archive exists. Exact queries and results are summarized in the manifest.

## 5. Feasible reconstruction plan and nonuniqueness

1. **Freeze the recovered candidate.** Keep the original ZIP, metadata, hashes and CRS. Use the named traffic-segment layer, rather than count stations or an unfiltered state-route layer. Record whether the historical byte identity remains unverified.
2. **Resolve route preparation before creating points.** “Joined by route numbers” does not specify `StateRouteNumber` versus `RouteIdentifier`, multipart/disconnected handling, branch order, coordinate direction, geometric union versus ordered merge, endpoint inclusion, or where the kilometre sequence starts. Record these choices explicitly; 188 versus 251 available keys demonstrates this ambiguity on the actual input.
3. **Recover or enumerate tunnel exclusions and joins.** Need the tunnel source/date or exact excluded point IDs; join predicate, distance/tolerance and tie-breaking at boundaries; treatment of coincident segments and duplicate points; and stable ID assignment. The script's `TARGET_FID` suggests an upstream GIS identifier, but does not identify the operation that produced it.
4. **Pin the DEM and boundary.** Need tile-edition list, exact state-boundary dataset/version (including water), UTM datum/transform, cell size, raster origin/alignment, target extent, resampling, mosaic precedence, NoData treatment and clip rule. Preserve full CRS WKT and raster geotransform. Do not infer these from the approximate 30 m description.
5. **Then validate a deliberately small corridor first**, in separate outputs with checked commands. Compare regenerated coordinates/AADT to any original CSV, including IDs and precision; compare raster metadata and checksums before viewsheds. This step is proposed, not executed. A chosen modern reconstruction must be labelled as such if original choices cannot be recovered.

**Why 11,225 is not enough (hand-derived argument):** on a straight 2.4 km route, sampling at 1.0 and 2.0 km from one end produces two points. Starting at the opposite end gives positions 0.4 and 1.4 km measured from the first end—also two points, with different coordinates. Network branches, phase, endpoints and tunnel removals add further choices. Equal counts constrain cardinality, not locations, weights or raster cells. Matching 11,225 by tuning exclusions would not validate reconstruction.

**Exact missing inputs:** original `points_to_analyze.csv`; original `clipped_nad83_1arcsec.tif` or its tile/boundary/grid manifest; original road export checksum or immutable snapshot; route merge/sampling settings; tunnel exclusions; spatial-join settings. The recovered 2019 FileGDB removes a major source-access obstacle. It does not recover those processing decisions or historical runtime events. Reconstruction could test sensitivity or reproduce a documented variant; it cannot by itself establish that Quinn encountered the previously identified failure path.

## Reproduce and resume

Run `python3 check_inputs.py` with `ogrinfo` installed. It reads preserved files, extracts the small ZIP into a temporary directory, checks schema-level counts/length and spatial-metadata contents, and performs no network request or viewshed calculation. [Actual output](CHECK-RESULTS.txt) and [hash/source manifest](MANIFEST.json) accompany this note. Source ZIP CRC and all checks passed. No large raster downloads, paid services, outreach, original destructive script or new workers were used.

Next useful action: obtain an independently archived processed CSV or provenance record specifying the missing decisions. If unavailable, agree on a clearly labelled reconstruction specification before any substantial computation. The intended historical reproduction remains **open**, while source recovery and the bounded metadata checks are complete.
