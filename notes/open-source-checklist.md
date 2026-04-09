# Open Source Checklist

This note tracks the repository cleanup done for the initial public-facing pass.

## Completed in this pass

- [x] Replaced the root `README.md` with a public project overview
- [x] Reworked the README toward a library/package presentation
- [x] Preserved the previous internal README content under `notes/`
- [x] Added a `notes/README.md` index so internal material stays discoverable
- [x] Kept the project under the MIT license already present in the repository
- [x] Prepared the package metadata for public hosting links and documentation references
- [x] Added GitHub Actions CI for package checks, builds, and source-distribution validation
- [x] Added contributor guidance and issue templates

## Good next steps

- [ ] Decide on a release/versioning story before the first public announcement
- [ ] Consider a changelog once the API starts stabilizing

## Positioning suggestion

Until the API stabilizes, describe TypedRedex as an experimental research prototype rather than a production-ready framework. That keeps expectations honest while still inviting interested users and collaborators.
