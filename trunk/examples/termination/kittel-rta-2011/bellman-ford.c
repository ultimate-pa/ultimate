#include <stdio.h>

int nondef(void);

typedef struct {
    int u, v, w;
} Edge;

Edge edges[1024]; /* large enough for n <= 2^5=32 */
int d[32]; /* d[i] is the minimum distance from node s to node i */

#define INFINITY 10000

void printDist(int n) {
    int i;

    printf("Distances:\n");

    for (i = 0; i < n; ++i)
        printf("to %d\t", i + 1);
    printf("\n");

    for (i = 0; i < n; ++i)
        printf("%d\t", d[i]);

    printf("\n\n");
}

void bellman_ford(int s, int n, int e) {
    int i, j;

    for (i = 0; i < n; ++i)
        d[i] = INFINITY;

    d[s] = 0;

    for (i = 0; i < n - 1; ++i)
        for (j = 0; j < e; ++j)
            if (d[edges[j].u] + edges[j].w < d[edges[j].v])
                d[edges[j].v] = d[edges[j].u] + edges[j].w;
}

int main() {
    int i, j;
    int w;

    int n; /* the number of nodes */
    int e; /* the number of edges */

    //FILE *fin = fopen("dist.txt", "r");
    //fscanf(fin, "%d", &n);
    n = nondef();
    e = 0;

    for (i = 0; i < n; ++i)
        for (j = 0; j < n; ++j) {
            //fscanf(fin, "%d", &w);
            w = nondef();
            if (w != 0) {
                edges[e].u = i;
                edges[e].v = j;
                edges[e].w = w;
                ++e;
            }
        }
    //fclose(fin);

    printDist(n);

    bellman_ford(0, n, e);

    printDist(n);

    return 0;
}
