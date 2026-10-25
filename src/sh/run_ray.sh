#!/usr/bin/env bash
set -euo pipefail

export RAY_PORT=64990
export DASHBOARD_PORT="${DASHBOARD_PORT:-8265}"
export RAY_TMPDIR_BASE="/tmp/ray_${SLURM_JOB_ID}"

# Worker port range (keep it tight & predictable on HPC)
export RAY_MIN_WORKER_PORT="${RAY_MIN_WORKER_PORT:-20000}"
export RAY_MAX_WORKER_PORT="${RAY_MAX_WORKER_PORT:-29999}"

# Put Ray "system" ports OUTSIDE worker range to avoid collision
export RAY_CLIENT_SERVER_PORT="${RAY_CLIENT_SERVER_PORT:-31001}"
export RAY_NODE_MANAGER_PORT="${RAY_NODE_MANAGER_PORT:-31002}"
export RAY_OBJECT_MANAGER_PORT="${RAY_OBJECT_MANAGER_PORT:-31003}"
export RAY_DASHBOARD_AGENT_GRPC_PORT="${RAY_DASHBOARD_AGENT_GRPC_PORT:-31004}"
export RAY_DASHBOARD_AGENT_HTTP_PORT="${RAY_DASHBOARD_AGENT_HTTP_PORT:-31005}"
export RAY_METRICS_EXPORT_PORT="${RAY_METRICS_EXPORT_PORT:-31006}"

VENV_ACTIVATE="ecp/bin/activate"

mapfile -t NODES < <(scontrol show hostnames "$SLURM_JOB_NODELIST")
HEAD_NODE=${NODES[0]}
WORKER_NODES=("${NODES[@]:1}")
HEAD_IP=$(getent hosts "$HEAD_NODE" | head -n1 | awk '{print $1}')

PARAMS_DIR="cache/params"
mkdir -p "$PARAMS_DIR"

ENV_FILE="${PARAMS_DIR}/ray_params_${SLURM_JOB_ID}.env"
cat > "$ENV_FILE" <<EOF
export RAY_PORT='${RAY_PORT}'
export DASHBOARD_PORT='${DASHBOARD_PORT}'
export RAY_TMPDIR_BASE='${RAY_TMPDIR_BASE}'
export HEAD_NODE='${HEAD_NODE}'
export HEAD_IP='${HEAD_IP}'
export RAY_ADDRESS='${HEAD_IP}:${RAY_PORT}'

# These are node-local settings. Do not export head-node values in the
# shared client env; each raylet gets its own values below before ray start.
unset RAY_OVERRIDE_NODE_IP_ADDRESS
unset RAY_NODE_IP_ADDRESS
unset VLLM_HOST_IP

# Recommended on clusters
export RAY_USAGE_STATS_ENABLED='0'

# Ports (avoid collisions)
export RAY_MIN_WORKER_PORT='${RAY_MIN_WORKER_PORT}'
export RAY_MAX_WORKER_PORT='${RAY_MAX_WORKER_PORT}'
export RAY_CLIENT_SERVER_PORT='${RAY_CLIENT_SERVER_PORT}'
export RAY_NODE_MANAGER_PORT='${RAY_NODE_MANAGER_PORT}'
export RAY_OBJECT_MANAGER_PORT='${RAY_OBJECT_MANAGER_PORT}'
export RAY_DASHBOARD_AGENT_GRPC_PORT='${RAY_DASHBOARD_AGENT_GRPC_PORT}'
export RAY_DASHBOARD_AGENT_HTTP_PORT='${RAY_DASHBOARD_AGENT_HTTP_PORT}'
export RAY_METRICS_EXPORT_PORT='${RAY_METRICS_EXPORT_PORT}'
EOF

echo "▶️  Starting Ray head on $HEAD_NODE ($HEAD_IP:$RAY_PORT)"

srun --nodes=1 --ntasks=1 --nodelist="$HEAD_NODE" --overlap \
bash -lc "
  set -euo pipefail
  source '$VENV_ACTIVATE'
  source '$ENV_FILE'

  export RAY_OVERRIDE_NODE_IP_ADDRESS='${HEAD_IP}'
  export RAY_NODE_IP_ADDRESS='${HEAD_IP}'
  export VLLM_HOST_IP='${HEAD_IP}'

  ray stop --force || true

  ray start --head \
    --node-ip-address='${HEAD_IP}' \
    --port='${RAY_PORT}' \
    --dashboard-host='127.0.0.1' \
    --dashboard-port='${DASHBOARD_PORT}' \
    --ray-client-server-port='${RAY_CLIENT_SERVER_PORT}' \
    --node-manager-port='${RAY_NODE_MANAGER_PORT}' \
    --object-manager-port='${RAY_OBJECT_MANAGER_PORT}' \
    --dashboard-agent-grpc-port='${RAY_DASHBOARD_AGENT_GRPC_PORT}' \
    --dashboard-agent-listen-port='${RAY_DASHBOARD_AGENT_HTTP_PORT}' \
    --metrics-export-port='${RAY_METRICS_EXPORT_PORT}' \
    --min-worker-port='${RAY_MIN_WORKER_PORT}' \
    --max-worker-port='${RAY_MAX_WORKER_PORT}' \
    --temp-dir='${RAY_TMPDIR_BASE}_head' \
    --disable-usage-stats \
    --block
" &

sleep 8

if [ "${#WORKER_NODES[@]}" -eq 0 ]; then
  echo "ℹ️  Only one node allocated. No workers to launch."
else
  i=0
  for NODE in "${WORKER_NODES[@]}"; do
    NODE_IP=$(getent hosts "$NODE" | head -n1 | awk '{print $1}')
    WORKER_TMPDIR="${RAY_TMPDIR_BASE}_worker_${i}"

    echo "🚀 Starting worker $i on $NODE ($NODE_IP) temp=${WORKER_TMPDIR}"

    srun --nodes=1 --ntasks=1 --nodelist="$NODE" --overlap \
    bash -lc "
      set -euo pipefail
      source '$VENV_ACTIVATE'
      source '$ENV_FILE'

      export RAY_OVERRIDE_NODE_IP_ADDRESS='${NODE_IP}'
      export RAY_NODE_IP_ADDRESS='${NODE_IP}'
      export VLLM_HOST_IP='${NODE_IP}'

      ray stop --force || true

      ray start --address='${HEAD_IP}:${RAY_PORT}' \
        --node-ip-address='${NODE_IP}' \
        --min-worker-port='${RAY_MIN_WORKER_PORT}' \
        --max-worker-port='${RAY_MAX_WORKER_PORT}' \
        --temp-dir='${WORKER_TMPDIR}' \
        --disable-usage-stats \
        --block
    " &

    i=$((i+1))
  done
fi

source "$ENV_FILE"
echo "✅ Ray cluster should be up. HEAD=${HEAD_IP}:${RAY_PORT}"
echo "   vLLM host IP is set per Ray node before ray start."
echo "   Source env: source '$ENV_FILE'"
