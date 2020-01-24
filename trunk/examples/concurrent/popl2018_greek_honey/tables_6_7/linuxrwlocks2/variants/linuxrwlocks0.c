#include <stdlib.h>
#include <pthread.h>
#include "../../../stdatomic.h"

#include "../linuxrwlocks.c"

int main()
{
	pthread_t t1, t2;
	atomic_init(&mylock.lock, RW_LOCK_BIAS);

	if (pthread_create(&t1, NULL, thread_reader_writer, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_reader_writer, NULL))
		abort();

	return 0;
}
