#!/bin/sh

# These move most user processes to CPUs 0 and 2, but some kernel stuff still runs there.
# Instead, boot the kernel with isolcpus=1,3 (press 'e' in GRUB).
# Not setting the nohz option because that makes switches into kernelspace more expensive (and those happen on page fault).
# sudo systemctl --runtime set-property system.slice AllowedCPUs=0,2
# sudo systemctl --runtime set-property user.slice AllowedCPUs=0,2

# The following commands do not seem to have any effect on the startup time of the Lean runtime.
# Disabling CPU 1 and turbo mode each seem to change the shape of the benchmark run time distribution slightly, but don't reduce variability or average duration.
# Just using CPU isolation and running the bench commands on CPU 3 with taskset -c 3 seems good enough.

# Disable CPU 1
echo 0 | sudo tee /sys/devices/system/cpu/cpu1/online

# Disable idle state for CPU 3
sudo cpupower --cpu 3 idle-set -D 0

# Performance mode for CPU 3
echo performance | sudo tee /sys/devices/system/cpu/cpu3/cpufreq/scaling_governor

# Disable turbo mode (on all CPUs)
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

# Set performance bias to maximum performance
sudo cpupower --cpu 3 set --perf-bias 0
