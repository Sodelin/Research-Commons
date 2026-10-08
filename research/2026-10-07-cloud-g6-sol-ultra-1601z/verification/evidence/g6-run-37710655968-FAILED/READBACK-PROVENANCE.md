# Terminal readback provenance

The authenticated GitHub connector returned the complete decoded log for job113095563411 of run37710655968. Its original UTF-8 content is preserved losslessly in actions.connector-job-original.log (1982427 bytes; SHA256 e9fd642d7e096da0582756452079334f03cee5175168f60c8e3f8b1b59d1f356). actions.log retains the same lines with an outer connector-stage prefix solely for the existing recovery parser. No source, diagnostic, command receipt or payload content is rewritten.

The frozen Git input, every custom/final-audit command stdout hash, selected axiom reports and full gzip/base64 environment payload authenticate exactly. Cache/progress stdout transport is excluded from stdout reconstruction. Source and stdout hashes establish the compiler scope; this outer log representation is not asserted byte-equal to separately retrieved GitHub step logs.

Artifact11521724380 metadata is preserved (991927 bytes; public SHA256 digest353befe463c041430fcc29f6b877f1418d5938aef29151e5354c0dd7a76e4a8b). No ZIP download or archive equality is claimed; no signed blob URL is retained. No new compiler job was launched during recovery.
