# rcmc
rcmc -rc11 --unroll=3 -- -DN=2 variants/main0.c
rcmc -wrc11 --unroll=3 -- -DN=2 variants/main0.c

# nidhugg
nidhuggc -DN=3 -- --sc --unroll=3 variants/main0.c
nidhuggc -DN=3 -- --tso --unroll=3 variants/main0.c
nidhuggc -DN=3 -- --pso --unroll=3 variants/main0.c
