atomic_int array[N+1];
int idx[N+1];

void *thread_reader(void *unused)
{
	int i = N;
	while (1) {
		if (atomic_load_explicit(&array[i], memory_order_acquire) == 0)
			break;
		__asm__ __volatile__("isync" ::: "memory");
		i--;
	}
	return NULL;
}

void *thread_writer(void *arg)
{
	int j = *((int *) arg);

	int r = atomic_load_explicit(&array[j - 1], memory_order_acquire) + 1;
	__asm__ __volatile__("isync" ::: "memory");
	__asm__ __volatile__("lwsync" ::: "memory");
	atomic_store_explicit(&array[j], r, memory_order_release);
	return NULL;
}
