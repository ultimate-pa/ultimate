#ifdef MAKE_ACCESSES_SC
# define mo_acquire memory_order_seq_cst
# define mo_release memory_order_seq_cst
#else
# define mo_acquire memory_order_acquire
# define mo_release memory_order_release
#endif

atomic_int x;
atomic_int y;
atomic_int z;
atomic_int w;

void *thread_one(void *arg)
{
	atomic_load_explicit(&x, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&y, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&z, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&w, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&x, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&y, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&z, mo_acquire);
	return NULL;
}

void *thread_two(void *arg)
{
	atomic_load_explicit(&x, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&y, mo_acquire);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_load_explicit(&z, mo_acquire);
	return NULL;
}

void *thread_three(void *arg)
{
	atomic_store_explicit(&x, 1, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&y, 1, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&x, 2, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&y, 2, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&x, 3, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&y, 3, mo_release);
	return NULL;
}

void *thread_four(void *arg)
{
	atomic_store_explicit(&z, 1, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&w, 1, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&z, 2, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&w, 2, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&z, 3, mo_release);
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&w, 3, mo_release);
	return NULL;
}
