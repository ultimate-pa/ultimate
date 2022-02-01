atomic_int x = ATOMIC_VAR_INIT(1);
atomic_int y = ATOMIC_VAR_INIT(1);

#define NUM 5

void *thread_1(void* arg)
{
	for (int i = 0; i < NUM; i++) {
		int prev_x = atomic_load_explicit(&x, memory_order_acquire);
		int prev_y = atomic_load_explicit(&y, memory_order_acquire);
		atomic_store_explicit(&x, prev_x + prev_y, memory_order_release);
	}
	return NULL;
}

void *thread_2(void* arg)
{
	for (int i = 0; i < NUM; i++) {
		int prev_x = atomic_load_explicit(&x, memory_order_acquire);
		int prev_y = atomic_load_explicit(&y, memory_order_acquire);
		atomic_store_explicit(&y, prev_x + prev_y, memory_order_release);
	}
	return NULL;
}

void *thread_3(void *arg)
{
	if (atomic_load_explicit(&x, memory_order_acquire) > 144 ||
	    atomic_load_explicit(&y, memory_order_acquire) > 144)
		assert(0);
	return NULL;
}
