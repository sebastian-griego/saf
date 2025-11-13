"""Helper utilities for preparing a Lean project before running tests."""

import os
import subprocess
from pathlib import Path
from typing import Dict, Optional


def _artifacts_exist(project_dir: Path) -> bool:
    """Return True if any compiled Lean artifacts (.olean) are present."""
    build_root = project_dir / ".lake" / "build" / "lib"
    if not build_root.exists():
        return False
    return any(build_root.rglob("*.olean"))


def ensure_project_built(project_dir: Path, verbose: bool = True) -> bool:
    """
    Check if the Lean project is built, and build it if necessary.
    
    Args:
        project_dir: Path to the Lean project directory
        verbose: If True, print status messages
        
    Returns:
        True if the project is built and ready, False otherwise
    """
    project_dir = Path(project_dir).resolve()
    artifacts_ready = _artifacts_exist(project_dir)
    
    if artifacts_ready:
        if verbose:
            print("✓ Project appears to be built")
        
        # Quick verification that Lean works. If this fails we fall back to building.
        try:
            result = subprocess.run(
                ["lake", "env", "lean", "--version"],
                cwd=str(project_dir),
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                if verbose:
                    print("✓ Lean environment is ready")
                return True
            if verbose:
                print("⚠ Lean environment check failed, rebuilding...")
        except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
            if verbose:
                print(f"⚠ Error checking Lean environment: {exc}, rebuilding...")
    else:
        if verbose:
            print("⚠ Build artifacts not found, building project...")
    
    if verbose:
        print("Building Lean project (this may take a few minutes)...")
    
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout for build
        )
        
        if result.returncode == 0:
            if verbose:
                print("✓ Project built successfully")
            return True
        if verbose:
            print(f"✗ Build failed:\n{result.stderr}")
        return False
    except subprocess.TimeoutExpired:
        if verbose:
            print("✗ Build timed out after 10 minutes")
        return False
    except FileNotFoundError:
        if verbose:
            print("✗ 'lake' command not found. Make sure Lean/Lake is installed and on PATH.")
        return False
    except Exception as exc:  # pragma: no cover - defensive logging
        if verbose:
            print(f"✗ Build error: {exc}")
        return False


def load_lake_environment(
    project_dir: Path,
    *,
    base_env: Optional[Dict[str, str]] = None,
    verbose: bool = True,
) -> Dict[str, str]:
    """
    Capture the environment variables produced by `lake env` once so we can run
    `lean` repeatedly without re-spawning `lake` (which is slow on large repos).
    """
    project_dir = Path(project_dir).resolve()
    if verbose:
        print("Computing Lean environment via `lake env` (one-time)...")
    try:
        proc = subprocess.run(
            ["lake", "env"],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            timeout=600,
            check=False,
        )
    except FileNotFoundError as exc:
        raise RuntimeError("'lake' command not found. Is Lean installed?") from exc
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError("`lake env` timed out while preparing environment") from exc
    
    if proc.returncode != 0:
        raise RuntimeError(f"`lake env` failed:\n{proc.stderr}")
    
    env = dict(base_env or os.environ)
    for line in proc.stdout.splitlines():
        if "=" not in line:
            continue  # skip warnings like "warning: repo ... has local changes"
        key, value = line.split("=", 1)
        env[key] = value
    if verbose:
        print("✓ Lean environment captured")
    return env

