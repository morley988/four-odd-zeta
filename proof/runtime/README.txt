Container-only executable-path compatibility shim.
Lean queried /proc/<its pid>/exe, unavailable under this container process mapping.
The shim resolves the current executable using AT_EXECFN, leaving all other
paths to libc. No proof code, elaborator or kernel is modified.
A normal Lean installation does not require this shim.
Build if needed with: cc -shared -fPIC -O2 proc_self_compat.c -ldl -o proc_self_compat.so
Set LD_PRELOAD to its absolute path only in the affected environment.
