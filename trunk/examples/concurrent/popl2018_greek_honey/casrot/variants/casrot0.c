#include <stdlib.h>
#include <pthread.h>
#include "../../../stdatomic.h"

#include "../casrot.c"

int main()
{
	pthread_t t[N];

	for (int i = 1; i < N + 1; i++) {
		idx[i - 1] = i;
		if (pthread_create(&t[i - 1], NULL, thread_n, &idx[i - 1]))
			abort();
	}

	return 0;
}
