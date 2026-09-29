#!/bin/bash
#SBATCH --job-name=hetero-dpsgd
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --gres=gpu:1
#SBATCH --cpus-per-task=10
#SBATCH --time=20:00:00
#SBATCH --output=%x-%A_%a.out
#SBATCH --error=%x-%A_%a.err

set -euo pipefail
cd "${SLURM_SUBMIT_DIR}"

if [[ $# -ne 1 ]]; then
  echo "usage: sbatch --array=1-N slurm/array.slurm JOB_FILE" >&2
  exit 2
fi

JOB_FILE=$1
COMMAND=$(sed -n "${SLURM_ARRAY_TASK_ID}p" "$JOB_FILE")
if [[ -z "$COMMAND" ]]; then
  echo "no command at line ${SLURM_ARRAY_TASK_ID} of ${JOB_FILE}" >&2
  exit 2
fi

# Use the submitting shell's environment, or a local virtual environment.
if [[ -f .venv/bin/activate ]]; then
  source .venv/bin/activate
fi
if ! python -c "import opacus" >/dev/null 2>&1; then
  echo "Missing dependencies: install requirements.txt and activate the environment before submission." >&2
  exit 1
fi

export OMP_NUM_THREADS=$SLURM_CPUS_PER_TASK
export PYTHONUNBUFFERED=1
export PYTHONDONTWRITEBYTECODE=1
export MPLCONFIGDIR
MPLCONFIGDIR=$(mktemp -d "${TMPDIR:-/tmp}/dpsgd-matplotlib.XXXXXX")

echo "$COMMAND"
# Do not reuse node-specific CPU masks from a parent job that submitted this job.
unset SLURM_CPU_BIND SLURM_CPU_BIND_LIST SLURM_CPU_BIND_TYPE SLURM_CPU_BIND_VERBOSE
srun --cpu-bind=none bash -c "$COMMAND"
