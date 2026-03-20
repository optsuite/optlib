1. Install elan, codex, git, python

2. Grant Codex permissions and trust this directory.

3. Update `lean-toolchain` to the latest version and run, and run `lake update -R`

4. Test the setup by running `lake build Mathlib`.

5. setup `WORKERS` environment variable and run `python3 pipeline.py`
