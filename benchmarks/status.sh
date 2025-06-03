#!/bin/sh

# These move most user processes to CPUs 0 and 2, but some kernel stuff still runs there.
# Instead, boot the kernel with isolcpus=1,3 (press 'e' in GRUB).
# Not setting the nohz option because that makes switches into kernelspace more expensive (and those happen on page fault).
# sudo systemctl --runtime set-property system.slice AllowedCPUs=0,2
# sudo systemctl --runtime set-property user.slice AllowedCPUs=0,2


# Disable CPU 1
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
