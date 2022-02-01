# rcmc
# mcs_spinlock(2)
rcmc -rc11 -unroll=3 -- -I. -DN=2 variants/main0.c
rcmc -wrc11 -unroll=3 -- -I. -DN=2 variants/main0.c

# mcs_spinlock(3)
rcmc -rc11 -unroll=4 -- -I. -DN=3 variants/main0.c
rcmc -wrc11 -unroll=4 -- -I. -DN=3 variants/main0.c

# nidhugg
# mcs_spinlock(2)
nidhuggc -I. -DN=2 -- --sc --unroll=3 variants/main0.c
nidhuggc -I. -DN=2 -- --tso --unroll=3 variants/main0.c
nidhuggc -I. -DN=2 -- --pso --unroll=3 variants/main0.c

# mcs_spinlock(3)
nidhuggc -I. -DN=3 -- --sc --unroll=4 variants/main0.c
nidhuggc -I. -DN=3 -- --tso --unroll=4 variants/main0.c
nidhuggc -I. -DN=3 -- --pso --unroll=4 variants/main0.c
