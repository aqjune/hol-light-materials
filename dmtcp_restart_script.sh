#!/bin/bash

set -m # turn on job control

#This script launches all the restarts in the background.
#Suggestions for editing:
#  1. For those processes executing on the localhost, remove
#     'ssh <hostname> from the start of the line.
#  2. If using ssh, verify that ssh does not require passwords or other
#     prompts.
#  3. Verify that the dmtcp_restart command is in your path on all hosts,
#     otherwise set the dmt_rstr_cmd appropriately.
#  4. Verify DMTCP_COORD_HOST and DMTCP_COORD_PORT match the location of
#     the dmtcp_coordinator. If necessary, add
#     'DMTCP_COORD_PORT=<dmtcp_coordinator port>' after
#     'DMTCP_COORD_HOST=<...>'.
#  5. Remove the '&' from a line if that process reads STDIN.
#     If multiple processes read STDIN then prefix the line with
#     'xterm -hold -e' and put '&' at the end of the line.
#  6. Processes on same host can be restarted with single dmtcp_restart
#     command.


check_local()
{
  worker_host=$1
  unset is_local_node
  worker_ip=$(gethostip -d $worker_host 2> /dev/null)
  if [ -z "$worker_ip" ]; then
    worker_ip=$(nslookup $worker_host | grep -A1 'Name:' | grep 'Address:' | sed -e 's/Address://' -e 's/ //' -e 's/    //')
  fi
  if [ -z "$worker_ip" ]; then
    worker_ip=$(getent ahosts $worker_host |grep "^[0-9]\+\.[0-9]\+\.[0-9]\+\.[0-9]\+ *STREAM" | cut -d' ' -f1)
  fi
  if [ -z "$worker_ip" ]; then
    echo Could not find ip-address for $worker_host. Exiting...
    exit 1
  fi
  ifconfig_path=$(which ifconfig)
  if [ -z "$ifconfig_path" ]; then
    ifconfig_path="/sbin/ifconfig"
  fi
  output=$($ifconfig_path -a | grep "inet addr:.*${worker_ip} .*Bcast")
  if [ -n "$output" ]; then
    is_local_node=1
  else
    is_local_node=0
  fi
}


pass_slurm_helper_contact()
{
  LOCAL_FILES="$1"
  # Create temp directory if needed
  if [ -n "$DMTCP_TMPDIR" ]; then
    CURRENT_TMPDIR=$DMTCP_TMPDIR/dmtcp-`whoami`@`hostname`
  elif [ -n "$TMPDIR" ]; then
    CURRENT_TMPDIR=$TMPDIR/dmtcp-`whoami`@`hostname`
  else
    CURRENT_TMPDIR=/tmp/dmtcp-`whoami`@`hostname`
  fi
  if [ ! -d "$CURRENT_TMPDIR" ]; then
    mkdir -p $CURRENT_TMPDIR
  fi
  # Create files with SLURM environment
  for CKPT_FILE in $LOCAL_FILES; do
    SUFFIX=${CKPT_FILE%%.dmtcp}
    SLURM_ENV_FILE=$CURRENT_TMPDIR/slurm_env_${SUFFIX##*_}
    echo "DMTCP_SRUN_HELPER_ADDR=$DMTCP_SRUN_HELPER_ADDR" >> $SLURM_ENV_FILE
  done
}


usage_str='USAGE:
  dmtcp_restart_script.sh [OPTIONS]

OPTIONS:
  --coord-host, -h, (environment variable DMTCP_COORD_HOST):
      Hostname where dmtcp_coordinator is running
  --coord-port, -p, (environment variable DMTCP_COORD_PORT):
      Port where dmtcp_coordinator is running
  --hostfile <arg0> :
      Provide a hostfile (One host per line, "#" indicates comments)
  --ckptdir, -d, (environment variable DMTCP_CHECKPOINT_DIR):
      Directory to store checkpoint images
      (default: use the same directory used in previous checkpoint)
  --restartdir, -d, (environment variable DMTCP_RESTART_DIR):
      Directory to read checkpoint images from
  --tmpdir, -t, (environment variable DMTCP_TMPDIR):
      Directory to store temporary files (default: $TMDPIR or /tmp)
  --no-strict-checking:
      Disable uid checking for checkpoint image. This allows the
      checkpoint image to be restarted by a different user than the one
      that created it.  And suppress warning about running as root.
      (environment variable DMTCP_DISABLE_STRICT_CHECKING)
  --interval, -i, (environment variable DMTCP_CHECKPOINT_INTERVAL):
      Time in seconds between automatic checkpoints
      (Default: Use pre-checkpoint value)
  --coord-logfile PATH (environment variable DMTCP_COORD_LOG_FILENAME
              Coordinator will dump its logs to the given file
  --help:
      Print this message and exit.'


ckpt_timestamp="Thu Nov 21 16:38:37 2024"

remote_shell_cmd="ssh"

coord_host=$DMTCP_COORD_HOST
if test -z "$DMTCP_COORD_HOST"; then
  coord_host=ip-172-31-12-40
fi

coord_port=$DMTCP_COORD_PORT
if test -z "$DMTCP_COORD_PORT"; then
  coord_port=7779
fi

checkpoint_interval=$DMTCP_CHECKPOINT_INTERVAL
if test -z "$DMTCP_CHECKPOINT_INTERVAL"; then
  checkpoint_interval=0
fi
export DMTCP_CHECKPOINT_INTERVAL=${checkpoint_interval}

if [ $# -gt 0 ]; then
  while [ $# -gt 0 ]
  do
    if [ $1 = "--help" ]; then
      echo "$usage_str"
      exit
    elif [ $# -ge 1 ]; then
      case "$1" in
        --coord-host|--host|-h)
          coord_host="$2"
          shift; shift;;
        --coord-port|--port|-p)
          coord_port="$2"
          shift; shift;;
        --coord-logfile)
          DMTCP_COORD_LOGFILE="$2"
          shift; shift;;
        --hostfile)
          hostfile="$2"
          if [ ! -f "$hostfile" ]; then
            echo "ERROR: hostfile $hostfile not found"
            exit
          fi
          shift; shift;;
        --restartdir|-d)
          DMTCP_RESTART_DIR=$2
          shift; shift;;
        --ckptdir|-d)
          DMTCP_CKPT_DIR=$2
          shift; shift;;
        --tmpdir|-t)
          DMTCP_TMPDIR=$2
          shift; shift;;
        --no-strict-checking)
          noStrictChecking="--no-strict-checking"
          shift;;
        --interval|-i)
          checkpoint_interval=$2
          shift; shift;;
        *)
          echo "$0: unrecognized option '$1'. See correct usage below"
          echo "$usage_str"
          exit;;
      esac
    elif [ $1 = "--help" ]; then
      echo "$usage_str"
      exit
    else
      echo "$0: Incorrect usage.  See correct usage below"
      echo
      echo "$usage_str"
      exit
    fi
  done
fi

dmt_rstr_cmd=/home/ubuntu/dmtcp/bin/dmtcp_restart
which $dmt_rstr_cmd > /dev/null 2>&1 || dmt_rstr_cmd=dmtcp_restart
which $dmt_rstr_cmd > /dev/null 2>&1 || echo "$0: $dmt_rstr_cmd not found"
which $dmt_rstr_cmd > /dev/null 2>&1 || exit 1

# Number of hosts in the computation = 1
# Number of processes in the computation = 3

given_ckpt_files=" /home/ubuntu/s2n-bignum/ckpt_bash_6b08fa09bc51a7d4-40000-2928fa164c17.dmtcp /home/ubuntu/s2n-bignum/ckpt_ledit_6b08fa09bc51a7d4-44000-2928fea2f61d.dmtcp /home/ubuntu/s2n-bignum/ckpt_ocamlrun_6b08fa09bc51a7d4-45000-2928ff1ee193.dmtcp"

ckpt_files=""
if [ ! -z "$DMTCP_RESTART_DIR" ]; then
  for tmp in $given_ckpt_files; do
    ckpt_files="$DMTCP_RESTART_DIR/$(basename $tmp) $ckpt_files"
  done
else
  ckpt_files=$given_ckpt_files
fi

coordinator_info="--coord-host $coord_host --coord-port $coord_port"
tmpdir=
if [ ! -z "$DMTCP_TMPDIR" ]; then
  tmpdir="--tmpdir $DMTCP_TMPDIR"
fi

ckpt_dir=
if [ ! -z "$DMTCP_CKPT_DIR" ]; then
  ckpt_dir="--ckptdir $DMTCP_CKPT_DIR"
fi

coord_logfile=
if [ ! -z "$DMTCP_COORD_LOGFILE" ]; then
  coord_logfile="--coord-logfile $DMTCP_COORD_LOGFILE"
fi

exec $dmt_rstr_cmd $coordinator_info $ckpt_dir \
  $maybejoin --interval "$checkpoint_interval" $tmpdir $noStrictChecking $coord_logfile\
  $ckpt_files
