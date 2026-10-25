from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1] / "encodings"
    for script in sorted(root.glob("timeout_P2026*.py")):
        print(f"RUN {script.name}", flush=True)
        subprocess.run([sys.executable, str(script)], cwd=root, check=True)


if __name__ == "__main__":
    main()
