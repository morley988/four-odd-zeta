# Provenance and contributions

This repository imports the completed Round 29 four-value zeta proof package and the manuscript revised 15 October 2026. The proof package's internal layout and bytes are preserved, except that two large tables are stored compressed and restored exactly before use.

The mathematical development, Lean implementation, numerical programs, exposition, and packaging were developed through an extended human-directed collaboration with ChatGPT/Codex. AI assistance is part of the project's provenance; it is not an independent reviewer or a substitute for the recorded verification boundary. Formal author names and contribution attribution remain for the repository owner to confirm.

The prior archive's 528-entry manifest is retained. New repository documentation and helper scripts are editorial/packaging additions; they add no mathematical assumption. No new Lean admission was added during import.

Historical progress reports are preserved and can describe superseded intermediate stages. For current conclusions use the root README, the latest manuscript, the final report, and the final theorem modules.

The original reproduction reused compiled artifacts. This import does not retrospectively turn it into a clean build. Future runs should identify the commit, toolchain, caches, exact commands, and results.

The runtime compatibility files under `proof/runtime/` are historical environment notes, not required Cloud setup steps. Third-party sources are fetched from pinned repositories rather than copied into this repository.
