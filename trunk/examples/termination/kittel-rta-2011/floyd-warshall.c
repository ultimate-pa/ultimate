int min(int i, int j)
{
    if (i < j) {
        return i;
    } else {
        return j;
    }
}

void floyd_warshall(int *dist[], int N)
{
    int i, j, k;
    // Input data into dist, where dist[i][j] is the distance from i to j.
    for (k = 0; k < N; k++) {
        for (i = 0; i < N; i++) {
            for (j = 0; j < N; j++) {
                dist[i][j] = min( dist[i][j], dist[i][k] + dist[k][j] );
            }
        }
    }

    // Now the shortest distance between i and j will be in dist[i][j].
}
