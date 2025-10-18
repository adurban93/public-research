#!/usr/bin/env python3
"""Local wrapper for running the Maps scraper via Oxylabs proxy."""

import importlib.util
import os
from pathlib import Path
import sys


DEFAULT_PROXY = os.getenv("OXYLABS_RESIDENTIAL_PROXY", "http://us-pr.oxylabs.io:10000")


def main() -> int:
    """Run the primary scraper with a proxy default suitable for local tests."""
    # Only set the default proxy if the caller didn't override it already.
    os.environ.setdefault("MAPS_PROXY", DEFAULT_PROXY)

    if "MAPS_LOCAL_ARTIFACT_DIR" not in os.environ:
        default_local_dir = Path.cwd() / "local_supabase_artifacts"
        default_local_dir.mkdir(parents=True, exist_ok=True)
        os.environ["MAPS_LOCAL_ARTIFACT_DIR"] = str(default_local_dir)

    # Load the main scraper module dynamically because the filename contains
    # hyphens, which prevents direct ``import`` syntax.
    module_path = Path(__file__).with_name("maps_parallel_scraper.py")
    spec = importlib.util.spec_from_file_location("maps_parallel_scraper", module_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Unable to load scraper module from {module_path}")
    scraper_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scraper_module)

    return scraper_module.main()


if __name__ == "__main__":
    sys.exit(main())
