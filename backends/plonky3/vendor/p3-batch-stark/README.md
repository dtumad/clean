# Local p3-batch-stark patch

This package is copied from Plonky3 commit
`47e442ffb5ad5f6c86f845e48283867f348243ba` and kept isolated from the Clean backend.

The local patch adds transcript-bound, verifier-known contributions to named global lookup buses.
This lets Clean represent its verifier program as public channel interactions without
manufacturing a one-row AIR and committed trace for it. The original `prove_batch` and
`verify_batch` APIs remain available; Clean uses the corresponding `*_with_public_lookups` entry
points.

Channels used only by public interactions have no trace lookup challenges. The verifier checks
their exact field balance separately for each message; repeated occurrences still enter the
transcript and Clean's occurrence bound. Channels shared with tables retain the lookup argument.
This change belongs in the existing batch verifier because an extension cannot change its
rejection of channels absent from physical AIRs. Remove the local patch once upstream supports
these public contributions, including channels with no physical users.
