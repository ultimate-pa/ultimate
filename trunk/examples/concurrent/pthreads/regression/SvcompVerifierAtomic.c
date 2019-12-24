//#Safe
/*
 * Check if we correctly support the __VERIFIER_atomic_begin(); and
 * __VERIFIER_atomic_end(); functions from the SV-COMP.
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-11-10
 * 
 */

#include <pthread.h>
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

typedef unsigned long int pthread_t;
int g = 0;

void *foo(void *arg) {
		g = g * 2;
        return (void*)NULL;
}

int main() {
        pthread_t threadId;
        pthread_create(&threadId, NULL, & foo, NULL);
		__VERIFIER_atomic_begin();
		g = g + 1;
		g = g - 1;
		__VERIFIER_atomic_end();
		if (g > 0) {
			//@ assert \false;
		}
		
}
