# rcmc
rcmc -rc11 --unroll=4 -- -DN=3 variants/main0.c
rcmc -wrc11 --unroll=4 -- -DN=3 variants/main0.c

# nidhugg
nidhuggc -DN=3 -- --sc --unroll=4 variants/linuxrwlocks0.c
nidhuggc -DN=3 -- --tso --unroll=4 variants/linuxrwlocks0.c
nidhuggc -DN=3 -- --pso --unroll=4 variants/linuxrwlocks0.c
