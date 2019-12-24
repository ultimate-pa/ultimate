//#Safe
/*
 * Simple check that we find the function "foo" also when it is
 * given as "& foo".
 * No specification given.
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-11-03
 * 
 */

#include <pthread.h>

typedef unsigned long int pthread_t;

void *foo(void *arg) {
        return (void*)NULL;
}

int main() {
        pthread_t threadId;
        pthread_create(&threadId, NULL, & foo, NULL);
}
