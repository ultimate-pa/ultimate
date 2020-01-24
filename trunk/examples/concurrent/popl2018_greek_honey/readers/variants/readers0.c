#include <stdlib.h>
#include <pthread.h>
#include "../../../stdatomic.h"

#include "../readers.c"

int main()
{
	pthread_t t[N+1];

	for (int i = 0; i <= N; i++)
                atomic_init(&idx[i], i);
	for (int i = 0; i <= N; i++) {
		if (i == 0) {
			if (pthread_create(&t[i], NULL, thread_writer, NULL))
				abort();
		} else {
			if (pthread_create(&t[i], NULL, thread_reader, &idx[i-1]))
				abort();
		}
	}

	for (int i = 0; i <= N; i++) {
		pthread_join(t[i], NULL);
	}

	return 0;
}
