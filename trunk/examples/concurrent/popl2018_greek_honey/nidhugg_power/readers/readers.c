atomic_int x;
atomic_int idx[N+1];

void *thread_writer(void *unused)
{
	atomic_store_explicit(&x, 42, memory_order_release);
	return NULL;
}

void *thread_reader(void *arg)
{
	int r = *((int *) arg);
	atomic_load_explicit(&x, memory_order_acquire);
	return NULL;
}
