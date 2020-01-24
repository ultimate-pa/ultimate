#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include "../../../stdatomic.h"

#include "../casw.c"

int main()
{
	pthread_t t[N];

	for (int i = 0; i < N; i++) {
		idx[i] = i;
		if (pthread_create(&t[i], NULL, thread_n, &idx[i]))
			abort();
	}

	return 0;
}
