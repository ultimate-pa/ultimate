atomic_int x;
int idx[N];

void *thread_n(void *arg)
{
	int r = 0, val = *((int *) arg);

	atomic_compare_exchange_strong_explicit(&x, &r, 1, memory_order_relaxed,
						memory_order_relaxed);
	atomic_store_explicit(&x, val + 3, memory_order_release);
	return NULL;
}
