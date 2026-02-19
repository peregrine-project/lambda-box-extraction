#!/bin/sh
echo 1 | sudo tee /sys/devices/system/cpu/cpu1/online

sudo cpupower --cpu 3 idle-set -E

echo powersave | sudo tee /sys/devices/system/cpu/cpu3/cpufreq/scaling_governor

echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

sudo cpupower --cpu 3 set --perf-bias 6
