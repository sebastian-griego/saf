# Ensure the Lean project is built before running tests
# This prevents slow automatic builds during test execution

param(
    [string]$ProjectDir = ".\harness\lean_project"
)

function Test-LeanArtifacts {
    param([string]$Dir)
    $buildRoot = Join-Path $Dir ".lake\build\lib"
    if (-not (Test-Path $buildRoot)) {
        return $false
    }
    $artifact = Get-ChildItem -Path $buildRoot -Filter "*.olean" -Recurse -ErrorAction SilentlyContinue | Select-Object -First 1
    return $null -ne $artifact
}

Write-Host "Checking if Lean project is built..." -ForegroundColor Cyan

$artifactsReady = Test-LeanArtifacts -Dir $ProjectDir
if ($artifactsReady) {
    Write-Host "✓ Project appears to be built" -ForegroundColor Green
    Write-Host "Running quick verification..." -ForegroundColor Cyan
} else {
    Write-Host "⚠ Build artifacts not found, building project..." -ForegroundColor Yellow
}

$needsBuild = -not $artifactsReady

Push-Location $ProjectDir
try {
    if (-not $needsBuild) {
        try {
            $null = lake env lean --version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Lean environment is ready" -ForegroundColor Green
                exit 0
            } else {
                Write-Host "⚠ Lean environment check failed, rebuilding..." -ForegroundColor Yellow
                $needsBuild = $true
            }
        } catch {
            Write-Host "⚠ Error checking Lean environment, rebuilding..." -ForegroundColor Yellow
            $needsBuild = $true
        }
    }

    if ($needsBuild) {
        Write-Host "Building Lean project (this may take a few minutes)..." -ForegroundColor Cyan
        lake build
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Project built successfully" -ForegroundColor Green
            exit 0
        } else {
            Write-Host "✗ Build failed" -ForegroundColor Red
            exit 1
        }
    }
} catch {
    Write-Host "✗ Build error: $_" -ForegroundColor Red
    exit 1
} finally {
    Pop-Location
}

