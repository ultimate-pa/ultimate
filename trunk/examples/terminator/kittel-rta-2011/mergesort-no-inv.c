#include <stdio.h>
#include <stdlib.h>

/* Merge sort 
 * The merge sort divides the array into two sub-arrays, sorts them and then
 * calls merge to merge the two arrays back together.
*/

void Merge(int a[], int b[], int c[], int m, int n)
{
    int i = 0, j = 0, k = 0;
    while (i < m && j < n) {
        if (a[i] < b[j]) {
            c[k++] = a[i++];
        } else {
            c[k++] = b[j++];
        }
    }

    while (i < m) {
        c[k++] = a[i++];
    }

    while (j < n) {
        c[k++] = b[j++];
    }
}

int is_power(int n)
{
    int m;
    for (m = 1; m < n; m *= 2);
    return (m == n);
}

void merge_sort(int key[], int n)
{
    int j, k, *w;
    if (!is_power(n)) {
        printf ("ERROR: Size of the array is not power of 2.");
        return;        
    }
    w = calloc(n, sizeof(int));
    for (k = 1; k < n; k *= 2) {
        for (j = 0; j < (n - k); j += 2 * k) {
            Merge(key + j, key + j + k, w + j, k, k);
        }             
        for (j = 0; j < n; j++) {
            key[j] = w[j];
        }
    }
    free(w);
}
