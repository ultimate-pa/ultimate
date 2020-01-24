atomic_int x;
int idx[N];

void *thread_n(void *arg)
{
	int new = *((int *) arg);
	int exp = new - 1;

	atomic_compare_exchange_strong_explicit(&x, &exp, new, memory_order_relaxed,
						memory_order_relaxed);
	return NULL;
}
