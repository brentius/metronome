# Generated simulation-output cleanup snapshot

Snapshot of 10 generated simulator directories (102 files), taken before repository cleanup. This is preserved output, not a new verification run. `manifest.json` records original paths and SHA-256 hashes, including the 38 paths previously tracked under `code/tests/lockstep/sim_build*/`.

`simulation_builds.zip`: 2338424 bytes; SHA-256 `c192025f1d203ba3b7193f58b9cb92213f7909c4dee9deb340834d6328a0ae2c`. ZIP CRC and every uncompressed file hash were checked before and after untracking. The original relative directory layout is retained for inspection or recovery into a scratch directory.

The generated files were removed from Git's index and covered by `/code/tests/**/sim_build*/` ignore rules. Local build/cache directories remain on disk: automatic approval review blocked the recursive cache-deletion command, without a more specific stated reason. No alternate deletion was attempted.

The root `README.md` was cleared at the user's request and remains user-owned. Source, template workflows, saved raw evidence and architecture files were preserved. Seven `.gitkeep` files in populated directories were removed.
