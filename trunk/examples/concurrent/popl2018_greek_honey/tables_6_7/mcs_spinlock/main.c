_Atomic(struct mcs_spinlock *) lock;

int shared;
int idx[N];
struct mcs_spinlock nodes[N];

void *thread_n(void *param)
{
	int i = *((int *) param);
	mcs_spin_lock(&lock, &nodes[i]);
	shared = 42;
	mcs_spin_unlock(&lock, &nodes[i]);
	return NULL;
}
