# rcmc
rcmc -rc11 --unroll=3 -- variants/linuxrwlocks0.c
rcmc -wrc11 --unroll=3 -- variants/linuxrwlocks0.c

# nidhugg
nidhuggc -- --sc --unroll=3 variants/linuxrwlocks0.c
nidhuggc -- --tso --unroll=3 variants/linuxrwlocks0.c
nidhuggc -- --pso --unroll=3 variants/linuxrwlocks0.c
