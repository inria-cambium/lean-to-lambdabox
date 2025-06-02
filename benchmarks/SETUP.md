These moved most user processes to CPUs 0 and 2, but some kernel stuff is still running there.
$ sudo systemctl --runtime set-property system.slice AllowedCPUs=0,2
$ sudo systemctl --runtime set-property user.slice AllowedCPUs=0,2

Booting the kernel with isolcpus=1,3 worked better (press 'e' in GRUB)! Not setting nohz because that makes switches into kernelspace more expensive (and those happen on page fault).

Disable CPU 1:
$ echo 0 | sudo tee /sys/devices/system/cpu/cpu1/online

Disable idle state for CPU 3:
$ sudo cpupower --cpu 3 idle-set -D 0

Performance mode for CPU 3:
$ echo performance | sudo tee /sys/devices/system/cpu/cpu3/cpufreq/scaling_governor

Disable turbo mode (on all CPUs):
$ echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

Set performance bias to maximum performance
$ sudo cpupower --cpu 3 set --perf-bias 0
