import os
import subprocess
import threading
import time

# List of ports to check and kill if occupied
PORTS_TO_FREE = [8080, 10080, 20080]

# Set up environment
env = os.environ.copy()
env["PORT"] = "10080"

# Log file path
log_path = os.path.expanduser("./apptainer_run_online.log")

# Open log file in append mode with line buffering
log_file = open(log_path, "a", buffering=1)

# Logging function
def log(msg):
    timestamp = time.strftime("[%Y-%m-%d %H:%M:%S]")
    log_file.write(f"{timestamp} {msg}\n")
    log_file.flush()

# Kill any processes using the given ports
def free_ports(ports):
    for port in ports:
        try:
            result = subprocess.run(
                ["lsof", "-ti", f"TCP:{port}"],
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                text=True
            )
            pids = result.stdout.strip().split("\n")
            for pid in filter(None, pids):
                log(f"Killing process {pid} on port {port}")
                subprocess.run(["kill", "-9", pid])
        except Exception as e:
            log(f"Error freeing port {port}: {e}")

# Free ports before deployment
free_ports(PORTS_TO_FREE)

# Apptainer command
command = [
    "apptainer", "exec",
    "--env", "PORT=10080",
    "--bind", f"{env['HOME']}:{env['HOME']}",
    "--bind", f"{env['SCRATCH']}:{env['SCRATCH']}",
    "--bind", f"{env['PROJECT']}:{env['PROJECT']}",
    f"{env['PROJECT']}/sandbox/code_sandbox_server.sif",
    "make", "run-online"
]

# Launch Apptainer
process = subprocess.Popen(
    command,
    env=env,
    stdout=log_file,
    stderr=subprocess.STDOUT,
    preexec_fn=os.setpgrp
)

log(f"Launched apptainer server with PID: {process.pid}")

# # Run socat after 20 seconds
# def delayed_socat():
#     try:
#         time.sleep(10)
#         log("Launching socat TCP forwarder from 0.0.0.0:20080 to 127.0.0.1:10080...")
#         subprocess.Popen(
#             ["socat", "TCP-LISTEN:20080,fork,reuseaddr,bind=0.0.0.0", "TCP:127.0.0.1:10080"],
#             stdout=subprocess.DEVNULL,
#             stderr=subprocess.DEVNULL,
#             preexec_fn=os.setpgrp
#         )
#         log("socat launched successfully.")
#     except Exception as e:
#         log(f"Error launching socat: {e}")

# # Start delayed socat in background
# threading.Thread(target=delayed_socat, daemon=True).start()
