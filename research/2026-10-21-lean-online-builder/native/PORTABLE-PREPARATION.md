# Published certificate inputs

The three-module preparation script now first reads the already published
lean/Astra/CommonCertificateKernel.lean. Its original Git-blob and SHA checks
remain intact. The old intake path remains a fallback for the existing phone
workspace. The original library bytes and both standalone certificate bytes
are unchanged.

The corrected published script was actually used to prepare a NEW source-only
three-module layout from this packet. No compiler ran. The verification target
still refuses before launch because the native runtime writer is UNBOUND.
This corrects a portable-input path mismatch; it does not reinterpret earlier
source preparation against the real intake tree as a compiler result.
