# Setup Guide — Frozen Toolchain Configuration

This document specifies the **exact** toolchain and dependency versions used for reproducible S0 normalization.

## Toolchain

**Lean Version**: `leanprover/lean4:v4.25.0-rc2`
- Specified in: `harness/lean_project/lean-toolchain`
- Install with: `elan toolchain install leanprover/lean4:v4.25.0-rc2`
- Verify: `lake env lean --version`

## Dependencies

**Mathlib4**: Commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8`
- Pinned in: `harness/lean_project/lakefile.lean`
- Locked in: `harness/lean_project/lake-manifest.json`

## Setup Steps

1. **Install elan** (Lean toolchain manager):
   ```powershell
   # Windows (PowerShell)
   Invoke-WebRequest https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -OutFile elan-init.ps1
   .\elan-init.ps1
   ```

2. **Install the exact Lean toolchain**:
   ```powershell
   elan toolchain install leanprover/lean4:v4.25.0-rc2
   elan default leanprover/lean4:v4.25.0-rc2
   ```

3. **Verify installation**:
   ```powershell
   lean --version
   lake --version
   ```
   Should show: `Lean (version 4.25.0-rc2, ...)`

4. **Set up the Lean project**:
   ```powershell
   cd harness\lean_project
   lake update
   lake build
   lake env lean --version
   ```

5. **Verify mathlib is pinned correctly**:
   ```powershell
   # Check that mathlib is at the correct commit
   cd .lake\packages\mathlib
   git rev-parse HEAD
   # Should output: 5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8
   ```

## Reproducibility

**Critical**: Commit `lake-manifest.json` to version control. This file locks all dependency versions for exact reproducibility.

- The `lean-toolchain` file ensures everyone uses the same Lean version (`v4.25.0-rc2`)
- The `lakefile.lean` pins mathlib to commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8`
- The `lake-manifest.json` locks all transitive dependencies
- Run `lake update` to restore exact versions from the manifest
- The `.lake/` directory is ignored (build artifacts), but `lake-manifest.json` is committed

## CI Setup

A GitHub Actions workflow is provided in `.github/workflows/ci.yml`. For other CI systems:

```yaml
# GitHub Actions example
- uses: leanprover/elan-setup@v1
  with:
    toolchain: leanprover/lean4:v4.25.0-rc2
- run: |
    cd harness/lean_project
    lake update
    lake build
    python ../check_s0.py --data ../../data --project . --out ../../reports/ci.json
```

The workflow:
1. Installs the exact Lean toolchain
2. Restores dependencies from `lake-manifest.json`
3. Builds the project
4. Runs the harness with S0 and S1
5. Uploads test results as artifacts

## Verification

Run the verification script to check your setup:

```powershell
cd harness\lean_project
..\..\scripts\verify_toolchain.ps1
```

This checks:
- Lean version matches `4.25.0-rc2`
- `lean-toolchain` file is present and correct
- Mathlib is pinned to the correct commit in `lake-manifest.json`

## Troubleshooting

- **Toolchain mismatch**: Ensure `lean-toolchain` file is present and contains the exact version
- **Mathlib version drift**: Run `lake update` to restore versions from `lake-manifest.json`
- **Build failures**: Clear `.lake` directory and run `lake update` again
- **Cache issues**: Use `lake exe cache get` to fetch prebuilt mathlib artifacts
- **Verification failures**: Run `scripts/verify_toolchain.ps1` to diagnose issues

