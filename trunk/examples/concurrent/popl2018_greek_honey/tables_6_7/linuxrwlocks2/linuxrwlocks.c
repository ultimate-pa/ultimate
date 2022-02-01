#ifdef MAKE_ACCESSES_SC
# define mo_relaxed memory_order_seq_cst
# define mo_acquire memory_order_seq_cst
# define mo_release memory_order_seq_cst
#else
# define mo_relaxed memory_order_relaxed
# define mo_acquire memory_order_acquire
# define mo_release memory_order_release
#endif

#define RW_LOCK_BIAS            0x00100000
#define WRITE_LOCK_CMP          RW_LOCK_BIAS

void __VERIFIER_assume(int);

/** Example implementation of linux rw lock along with 2 thread test
 *  driver... */

typedef union {
	atomic_int lock;
} rwlock_t;

static inline int read_can_lock(rwlock_t *lock)
{
	return atomic_load_explicit(&lock->lock, mo_relaxed) > 0;
}

static inline int write_can_lock(rwlock_t *lock)
{
	return atomic_load_explicit(&lock->lock, mo_relaxed) == RW_LOCK_BIAS;
}

static inline void read_lock(rwlock_t *rw)
{
	int priorvalue = atomic_fetch_sub_explicit(&rw->lock, 1, mo_acquire);
	while (priorvalue <= 0) {
		atomic_fetch_add_explicit(&rw->lock, 1, mo_relaxed);
		/* while (atomic_load_explicit(&rw->lock, mo_relaxed) <= 0) */
		/* 	; //thrd_yield(); */
		__VERIFIER_assume(atomic_load_explicit(&rw->lock, mo_relaxed) >0);
		priorvalue = atomic_fetch_sub_explicit(&rw->lock, 1, mo_acquire);
	}
}

static inline void write_lock(rwlock_t *rw)
{
	int priorvalue = atomic_fetch_sub_explicit(&rw->lock, RW_LOCK_BIAS, mo_acquire);
	while (priorvalue != RW_LOCK_BIAS) {
		atomic_fetch_add_explicit(&rw->lock, RW_LOCK_BIAS, mo_relaxed);
		/* while (atomic_load_explicit(&rw->lock, mo_relaxed) != RW_LOCK_BIAS) */
		/* 	; //thrd_yield(); */
		__VERIFIER_assume(atomic_load_explicit(&rw->lock, mo_relaxed) == RW_LOCK_BIAS);
		priorvalue = atomic_fetch_sub_explicit(&rw->lock, RW_LOCK_BIAS, mo_acquire);
	}
}

static inline int read_trylock(rwlock_t *rw)
{
	int priorvalue = atomic_fetch_sub_explicit(&rw->lock, 1, mo_acquire);
	if (priorvalue > 0)
		return 1;

	atomic_fetch_add_explicit(&rw->lock, 1, mo_relaxed);
	return 0;
}

static inline int write_trylock(rwlock_t *rw)
{
	int priorvalue = atomic_fetch_sub_explicit(&rw->lock, RW_LOCK_BIAS, mo_acquire);
	if (priorvalue == RW_LOCK_BIAS)
		return 1;

	atomic_fetch_add_explicit(&rw->lock, RW_LOCK_BIAS, mo_relaxed);
	return 0;
}

static inline void read_unlock(rwlock_t *rw)
{
	atomic_fetch_add_explicit(&rw->lock, 1, mo_release);
}

static inline void write_unlock(rwlock_t *rw)
{
	atomic_fetch_add_explicit(&rw->lock, RW_LOCK_BIAS, mo_release);
}

rwlock_t mylock;
int shareddata;

void *thread_reader(void *unused)
{
	read_lock(&mylock);
	int r = shareddata;
	read_unlock(&mylock);
	return NULL;
}

void *thread_writer(void *unused)
{
	write_lock(&mylock);
	shareddata = 42;
	write_unlock(&mylock);
	return NULL;
}

void *thread_reader_writer(void *unused)
{
	read_lock(&mylock);
	int r = shareddata;
	read_unlock(&mylock);
	write_lock(&mylock);
	shareddata = 42;
	write_unlock(&mylock);
	return NULL;
}
