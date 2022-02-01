atomic_int x;
atomic_int y;
atomic_int z;
atomic_int w;

void *thread_one(void *arg)
{
	atomic_load_explicit(&x, memory_order_acquire);
	atomic_load_explicit(&y, memory_order_acquire);
	atomic_load_explicit(&z, memory_order_acquire);
	atomic_load_explicit(&w, memory_order_acquire);
	atomic_load_explicit(&x, memory_order_acquire);
	atomic_load_explicit(&y, memory_order_acquire);
	atomic_load_explicit(&z, memory_order_acquire);
	return NULL;
}

void *thread_two(void *arg)
{
	atomic_load_explicit(&x, memory_order_acquire);
	atomic_load_explicit(&y, memory_order_acquire);
	atomic_load_explicit(&z, memory_order_acquire);
	return NULL;
}

void *thread_three(void *arg)
{
	atomic_store_explicit(&x, 1, memory_order_release);
	atomic_store_explicit(&y, 1, memory_order_release);
	atomic_store_explicit(&x, 2, memory_order_release);
	atomic_store_explicit(&y, 2, memory_order_release);
	atomic_store_explicit(&x, 3, memory_order_release);
	atomic_store_explicit(&y, 3, memory_order_release);
	return NULL;
}

void *thread_four(void *arg)
{
	atomic_store_explicit(&z, 1, memory_order_release);
	atomic_store_explicit(&w, 1, memory_order_release);
	atomic_store_explicit(&z, 2, memory_order_release);
	atomic_store_explicit(&w, 2, memory_order_release);
	atomic_store_explicit(&z, 3, memory_order_release);
	atomic_store_explicit(&w, 3, memory_order_release);
	return NULL;
}
