#include <stdlib.h>

int nondef(void);

void mmain(int n) {
    int i, j, z;
    int *a = malloc(n * sizeof(int));
    for(i = 0;i< n-1;i++){
        a[i] = nondef();
    }
    for (i = 0; i < n - 1; i++) {
        for (j = i + 1; j < n; j++) {
            if(a[i]< a[j]){
                z = a[i]; a[i] = a[j]; a[j] = z;
            }
        }
    }
    for(i = 0;i< n -1;i++){
    }
}
