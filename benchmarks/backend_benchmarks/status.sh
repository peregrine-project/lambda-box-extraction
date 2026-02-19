#!/bin/sh

echo -n "CPU 1 (1: online, 0: offline): "
cat /sys/devices/system/cpu/cpu1/online

echo "CPU 3 idle states:"
cpupower --cpu 3 idle-info | ag "^C[0-9]|^P" --nocolor

echo -n "CPU 3 scaling governor: "
cat /sys/devices/system/cpu/cpu3/cpufreq/scaling_governor

echo -n "Turbo (1: disabled, 0: enabled): "
cat /sys/devices/system/cpu/intel_pstate/no_turbo

echo -n "CPU 3 energy/performance bias (0: max performance, 6: standard): "
cat /sys/devices/system/cpu/cpu3/power/energy_perf_bias
