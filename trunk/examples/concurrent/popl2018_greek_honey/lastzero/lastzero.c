atomic_int array[N+1];
int idx[N+1];

void *thread_reader(void *unused)
{
	for (int i = N; atomic_load_explicit(&array[i], memory_order_acquire) != 0; i--)
		;
	return NULL;
}

void *thread_writer(void *arg)
{
	int j = *((int *) arg);

	atomic_store_explicit(&array[j],
			      atomic_load_explicit(&array[j - 1], memory_order_acquire) + 1,
			      memory_order_release);
	return NULL;
}
