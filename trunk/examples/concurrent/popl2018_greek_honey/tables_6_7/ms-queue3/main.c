#include "my_queue.c"

static queue_t *queue;
static int num_threads;

queue_t myqueue;
int param[N];
unsigned int input[N];
unsigned int output[N];
pthread_t threads[N];

int get_thread_num()
{
	pthread_t curr = pthread_self();
	for (int i = 0; i < num_threads; i++)
		if (curr == threads[i])
			return i;
	assert(0);
}

bool succ[N];

void *task_enqueue(void *param)
{
	unsigned int val;
	int pid = *((int *)param);

	input[pid] = pid * 10;
	enqueue(queue, input[pid]);
	//	succ[pid] = dequeue(queue, &output[pid]);
	//printf("Dequeue: %d\n", output[0]);
	return NULL;
}

void *task_dequeue(void *param)
{
	unsigned int val;
	int pid = *((int *)param);

	input[pid] = pid * 10;
	//	enqueue(queue, input[pid]);
	succ[pid] = dequeue(queue, &output[pid]);
	//printf("Dequeue: %d\n", output[0]);
	return NULL;
}

void *task_enqueue_dequeue(void *param)
{
	unsigned int val;
	int pid = *((int *)param);

	input[pid] = pid * 10;
	enqueue(queue, input[pid]);
	succ[pid] = dequeue(queue, &output[pid]);
	//printf("Dequeue: %d\n", output[0]);
	return NULL;
}
