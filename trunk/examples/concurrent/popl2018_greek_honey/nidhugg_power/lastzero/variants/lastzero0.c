#include <stdlib.h>
#include <pthread.h>
#include "../../../stdatomic.h"

#include "../lastzero.c"

int main()
{
	pthread_t t[N+1];

	for (int i = 0; i <= N; i++) {
		idx[i] = i;
		if (i == 0) {
			if (pthread_create(&t[i], NULL, thread_reader, &idx[i]))
				abort();
		} else {
			if (pthread_create(&t[i], NULL, thread_writer, &idx[i]))
				abort();
		}
	}

	return 0;
}
