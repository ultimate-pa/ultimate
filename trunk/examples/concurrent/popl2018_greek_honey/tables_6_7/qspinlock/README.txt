# rcmc
# qspinlock(2)
rcmc -unroll=3 -rc11 -- -I. -I../mcs_spinlock -DN=2 variants/main0.c
rcmc -unroll=3 -wrc11 -- -I. -I../mcs_spinlock -DN=2 variants/main0.c

# qspinlock(3)
rcmc -unroll=4 -rc11 -- -I. -I../mcs_spinlock -DN=3 variants/main0.c
rcmc -unroll=4 -wrc11 -- -I. -I../mcs_spinlock -DN=3 variants/main0.c

# nidhugg
# qspinlock(2)
nidhuggc -I. -I../mcs_spinlock -DN=2 -- --sc --unroll=3 variants/main0.c
nidhuggc -I. -I../mcs_spinlock -DN=2 -- --tso --unroll=3 variants/main0.c
nidhuggc -I. -I../mcs_spinlock -DN=2 -- --pso --unroll=3 variants/main0.c

# qspinlock(3)
nidhuggc -I. -I../mcs_spinlock -DN=3 -- --sc --unroll=4 variants/main0.c
nidhuggc -I. -I../mcs_spinlock -DN=3 -- --tso --unroll=4 variants/main0.c
nidhuggc -I. -I../mcs_spinlock -DN=3 -- --pso --unroll=4 variants/main0.c
