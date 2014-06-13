#include <stdio.h>

#define GRAPHSIZE 2048
#define INFINITY GRAPHSIZE*GRAPHSIZE
#define MAX(a, b) ((a > b) ? (a) : (b))

int nondef();

int dist[GRAPHSIZE][GRAPHSIZE]; /* dist[i][j] is the distance between node i and j; or 0 if there is no direct connection */
int d[GRAPHSIZE]; /* d[i] is the length of the shortest path between the source (s) and node i */

void printD(int n) {
    int i;
    for (i = 1; i <= n; ++i)
        printf("%10d", i);
    printf("\n");
    for (i = 1; i <= n; ++i) {
        printf("%10d", d[i]);
    }
    printf("\n");
}

void dijkstra(int s, int n) {
    int i, k, mini;
    int visited[GRAPHSIZE];

    for (i = 1; i <= n; ++i) {
        d[i] = INFINITY;
        visited[i] = 0; /* the i-th element has not yet been visited */
    }

    d[s] = 0;

    for (k = 1; k <= n; ++k) {
        mini = -1;
        for (i = 1; i <= n; ++i)
            if (!visited[i] && ((mini == -1) || (d[i] < d[mini])))
                mini = i;

        visited[mini] = 1;

        for (i = 1; i <= n; ++i)
            if (dist[mini][i])
                if (d[mini] + dist[mini][i] < d[i])
                    d[i] = d[mini] + dist[mini][i];
    }
}

int main() {
    int i, j;
    int u, v, w;

    int e; /* The number of nonzero edges in the graph */
    int n; /* The number of nodes in the graph */

    //FILE *fin = fopen("dist.txt", "r");
    //fscanf(fin, "%d", &e);
    e = nondef();
    for (i = 0; i < e; ++i)
        for (j = 0; j < e; ++j)
            dist[i][j] = 0;
    n = -1;
    for (i = 0; i < e; ++i) {
        //fscanf(fin, "%d%d%d", &u, &v, &w);
        u = nondef();
        v = nondef();
        w = nondef();
        dist[u][v] = w;
        n = MAX(u, MAX(v, n));
    }
    //fclose(fin);

    dijkstra(1, n);

    printD(n);

    return 0;
}
