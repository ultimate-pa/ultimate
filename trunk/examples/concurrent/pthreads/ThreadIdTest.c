#include <pthread.h>
#include <stdio.h>
#include <assert.h>

typedef unsigned long int pthread_t;


void *inc(void *n) {
    int *ret = (int *)n;
    printf("%d\n", *ret);
    (*ret)++;
    printf("%d\n", *ret);
    return (void *)ret;
}

void *dec(void *n) {
    int *ret = (int *)n;
	(*ret)--;
    return (void *)ret;
}

int main() {
    pthread_t first_th_id;
    pthread_t second_th_id;
    int x = 0;
    pthread_create(&first_th_id, NULL, inc, &x);
    pthread_create(&second_th_id, NULL, dec, &x);

    void *y;
    pthread_join(first_th_id, &y);
    int *final = (int *)y;
    printf("%d\n", *final);
	//@ assert \false;
    
    return 0;
}
