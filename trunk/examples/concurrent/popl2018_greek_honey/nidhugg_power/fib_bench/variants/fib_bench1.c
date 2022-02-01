#include <assert.h>
#include <pthread.h>
#include "../../../stdatomic.h"

#include "../fib_bench.c"

int main()
{
	pthread_t t1, t2, t3;

	pthread_create(&t1, NULL, thread_1, NULL);
	pthread_create(&t3, NULL, thread_3, NULL);
	pthread_create(&t2, NULL, thread_2, NULL);

	return 0;
}
