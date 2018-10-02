#include <pthread.h>
#include <stdio.h>

void *bar(void *b) {
    printf("Created thread bar\n");
    int x = 0;
    while (x < 900000) {
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
    while (x < 90) {
        x++;
    }
    return (void *)"sam";
}

int main() {
    pthread_t thread_id;

    pthread_create(&thread_id, NULL, bar, NULL);
    pthread_create(&thread_id, NULL, foo, NULL);
    pthread_create(&thread_id, NULL, sam, NULL);

    void *joined_name = "";
    pthread_join(thread_id, &joined_name);
    printf("Finished Program and joined %s.\n", joined_name);
    
    return 0;
}