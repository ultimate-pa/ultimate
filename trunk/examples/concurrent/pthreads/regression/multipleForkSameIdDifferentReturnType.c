//#Unsafe
/*
 * Author: Lars Nitzke, 
 *         Matthias Heizmann (heizmann@informatik.uni-freiburg.de),
 *         Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: Spring 2019
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;


void *bar(void *b) {
    printf("Created thread bar\n");
    int x = 0;
    while (x < 2) {
        x++;
    }
    printf("Finished thread bar\n");
    return (void *)"bar";
}

void *foo(void *a) {
    printf("Created Thread foo\n");
    return (void *)"foo";
}

void *sam(void *c) {
    printf("Created thread sam\n");
    int x = 0;
    while (x < 3) {
        x++;
    }
    return (void *)"sam";
}

int main() {
    pthread_t thread_id;

    pthread_create(&thread_id, NULL, bar, NULL);
    pthread_create(&thread_id, NULL, foo, NULL);
    pthread_create(&thread_id, NULL, sam, NULL);

    char *joined_name = "";
    pthread_join(thread_id, &joined_name);
    printf("Finished Program and joined %s.\n", joined_name);

    // Join writes correct value ('f' == 102, 'b' == 98)
    char val = *joined_name;
    //@ assert val == 102 || val == 98;
    
    return 0;
}
