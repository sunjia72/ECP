from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1] / "encodings"
    scripts = sorted(p for p in root.glob("P2026AIME*.py") if p.name != Path(__file__).name)
    for script in scripts:
        print(f"RUN {script.name}", flush=True)
        subprocess.run([sys.executable, str(script)], cwd=root, check=True)


if __name__ == "__main__":
    main()
