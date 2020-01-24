arch_spinlock_t lock;

int shared;
int idx[N];

void *thread_n(void *param)
{
	int i = *((int *) param);
	set_cpu(i);

	arch_spin_lock(&lock);
	shared = 42;
	arch_spin_unlock(&lock);
	return NULL;
}
