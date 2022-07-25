#!/usr/bin/python

import os

FUZZER_ARGS = ["-heuristics", "transitions", "-mut", "own", "simplifications", "solving_parameters"]
FUZZER_ID = 300
SEEDS = 'all'

LOG_PATH = 'logs'
SEED_PATH = 'seed_info'
WORKDIR_PATH = 'work-dir'

# IMAGE_NAME = 'spacer-fuzzer'
IMAGE_NAME = 'conyashka/horny-fuzz:latest'

option_suffix = '-'.join(it.strip('-') for it in FUZZER_ARGS)
log_file = os.path.join(os.getcwd(), LOG_PATH, f'log-{FUZZER_ID}-{option_suffix}')
workdir = os.path.join(os.getcwd(), WORKDIR_PATH, f'fuzzer-workdir-{FUZZER_ID}-{option_suffix}')
seed_info_dir = os.path.join(os.getcwd(), SEED_PATH)
memory_analyzer_path = os.path.join(os.getcwd(), 'memory_analyzer_out')

docker_command = ["python", "src/main.py", SEEDS] + FUZZER_ARGS
#docker_command = ["/bin/bash"]
docker_path_mapping = {
    log_file: '/logfile',
    # seed_info_dir: '/seed_info',
    workdir: '/output',
    memory_analyzer_path: '/memory_analyzer_out'
}

docker_path_mapping_arg = ' '.join(f'-v {host}:{container}' for host, container in docker_path_mapping.items())
docker_command_arg = ' '.join(docker_command)
docker_permissions_arg = '--cap-add=SYS_PTRACE --security-opt seccomp=unconfined'

docker_full_command = f'docker run --rm -it {docker_path_mapping_arg} {docker_permissions_arg} {IMAGE_NAME} {docker_command_arg}'

if not os.path.exists(log_file):
    os.makedirs(os.path.dirname(log_file), exist_ok=True)
    open(log_file, 'a').close()

os.system(docker_full_command)
