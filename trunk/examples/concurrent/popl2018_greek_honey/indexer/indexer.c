#define SIZE 128
#define MAX  4

atomic_int table[SIZE];

void *thread_n(void *arg)
{
	int tid = *((int *) arg);
	int zero = 0;
	int w, h;

	for (int i = 0; i < MAX; i++) {
		w = i * 11 + tid;

		h = (w * 7) % SIZE;

		if (h < 0)
			assert(0);

		while (!atomic_compare_exchange_strong_explicit(&table[h], &zero, w,
								memory_order_relaxed,
								memory_order_relaxed)) {
			h = (h+1) % SIZE;
			zero = 0;
		}
	}
	return NULL;
}
