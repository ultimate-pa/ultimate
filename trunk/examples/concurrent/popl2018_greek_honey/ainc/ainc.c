atomic_int x;

void *thread_n(void *unused)
{
	atomic_fetch_add_explicit(&x, 1, memory_order_relaxed);
	return NULL;
}
