#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>
#include <stdbool.h>
#include <assert.h>
#include "../../../stdatomic.h"

#include "../main.c"

int main()
{
	int i;
	unsigned int in_sum = 0, out_sum = 0;

	queue = &myqueue;;
	num_threads = N;

	init_queue(queue, num_threads);
	for (i = 0; i < num_threads; i++) {
		param[i] = i;
		//		pthread_create(&threads[i], NULL, main_task, &param[i]);
	}

	pthread_create(&threads[0], NULL, task_enqueue, &param[0]);
	pthread_create(&threads[1], NULL, task_enqueue, &param[1]);
	pthread_create(&threads[2], NULL, task_enqueue_dequeue, &param[2]);

	/* for (i = 0; i < num_threads; i++) { */
	/* 	in_sum += input[i]; */
	/* 	out_sum += output[i]; */
	/* } */
	/* for (i = 0; i < num_threads; i++) */
	/* 	printf("input[%d] = %u\n", i, input[i]); */
	/* for (i = 0; i < num_threads; i++) */
	/* 	printf("output[%d] = %u\n", i, output[i]); */
	/* if (succ1 && succ2) */
	/* 	assert(in_sum == out_sum); */
	/* else */
	/* 	assert(0); */

	return 0;
}
