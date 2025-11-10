# Verify that the toolchain is set up correctly with frozen versions

Write-Host "=== Toolchain Verification ===" -ForegroundColor Cyan
Write-Host ""

# Check Lean version
Write-Host "Checking Lean version..." -ForegroundColor Yellow
$leanOutput = lake env lean --version 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "Lean version: $leanOutput" -ForegroundColor Green
    if ($leanOutput -match "4\.25\.0-rc2") {
        Write-Host "  Correct version (4.25.0-rc2)" -ForegroundColor Green
    } else {
        Write-Host "  Wrong version! Expected 4.25.0-rc2" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "Lean not found or error" -ForegroundColor Red
    exit 1
}

Write-Host ""

# Check toolchain file
$toolchainFile = "lean-toolchain"
if (Test-Path $toolchainFile) {
    $toolchain = Get-Content $toolchainFile -Raw
    Write-Host "Found lean-toolchain file" -ForegroundColor Green
    Write-Host "  Content: $($toolchain.Trim())" -ForegroundColor Gray
} else {
    Write-Host "lean-toolchain file not found" -ForegroundColor Red
    exit 1
}

Write-Host ""

# Check mathlib commit
Write-Host "Checking mathlib version..." -ForegroundColor Yellow
$manifestFile = "lake-manifest.json"
if (Test-Path $manifestFile) {
    $manifest = Get-Content $manifestFile -Raw | ConvertFrom-Json
    $mathlib = $manifest.packages | Where-Object { $_.name -eq "mathlib" }
    if ($mathlib) {
        $expectedRev = "5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8"
        if ($mathlib.rev -eq $expectedRev) {
            Write-Host "Mathlib commit: $($mathlib.rev)" -ForegroundColor Green
            Write-Host "  Correct commit" -ForegroundColor Green
        } else {
            Write-Host "Mathlib commit mismatch!" -ForegroundColor Red
            Write-Host "  Expected: $expectedRev" -ForegroundColor Red
            Write-Host "  Found: $($mathlib.rev)" -ForegroundColor Red
            exit 1
        }
    } else {
        Write-Host "Mathlib not found in manifest" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "lake-manifest.json not found" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "=== All checks passed! ===" -ForegroundColor Green

