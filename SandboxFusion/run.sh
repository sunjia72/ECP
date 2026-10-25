#!/bin/bash
#SBATCH -A def-ksmeel
#SBATCH -t 12:00:00
#SBATCH -c 192
#SBATCH --mem=100G
#SBATCH --nodes=1
#SBATCH -D $PROJECT                # job starts in project root
#SBATCH --job-name=sf
#SBATCH --output=$PROJECT/output/slurm/sf_%j.out
#SBATCH --error=$PROJECT/output/slurm/sf_%j.err

set -euxo pipefail

# === Paths ===
PROJECT=$PROJECT
SF_DIR="$PROJECT/logic/SandboxFusion"
SIF_PATH="$PROJECT/sandbox/code_sandbox_server.sif"        # same as in Python
RUN_PY="$SF_DIR/run_no_background.py"

# Ensure output dir exists
mkdir -p "$SF_DIR/slurm_output"

# Module (adjust if your cluster uses a different name/version)
module load apptainer/1.3.5 || true

# Avoid ROCm env leakage on NVIDIA nodes
unset ROCR_VISIBLE_DEVICES || true

# Optional: set/override PORT for the Python runner

# Always run the Python launcher from the SandboxFusion directory
cd "$SF_DIR"

# Launch
python "$RUN_PY"
