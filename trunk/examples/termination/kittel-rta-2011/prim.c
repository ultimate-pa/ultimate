#include <stdio.h>

int nondef(void);

int weight[100][100]; /* weight[i][j] is the distance between node i and node j;
                       * if there is no path between i and j, weight[i][j]
                       * should be 0 */

char inTree[100]; /* inTree[i] is 1 if the node i is already in the minimum
                   * spanning tree; 0 otherwise*/

int d[100]; /* d[i] is the distance between node i and the minimum spanning
             * tree; this is initially infinity (100000); if i is already in
             * the tree, then d[i] is undefined;
             * this is just a temporary variable. It's not necessary but speeds
             * up execution considerably (by a factor of n) */

int whoTo[100]; /* whoTo[i] holds the index of the node i would have to be
                 * linked to in order to get a distance of d[i] */

/* updateDistances(int target)
 * should be called immediately after target is added to the tree;
 * updates d so that the values are correct (goes through target's
 * neighbours making sure that the distances between them and the tree
 * are indeed minimum)
 * */
void updateDistances(int target, int n) {
    int i;
    for (i = 0; i < n; ++i)
        if ((weight[target][i] != 0) && (d[i] > weight[target][i])) {
            d[i] = weight[target][i];
            whoTo[i] = target;
        }
}

int main() {
    int n; /* The number of nodes in the graph */

    //FILE *f = fopen("dist.txt", "r");
    //fscanf(f, "%d", &n);
    n = nondef();
    int i, j;
    for (i = 0; i < n; ++i)
        for (j = 0; j < n; ++j)
            weight[i][j] = nondef();
            //fscanf(f, "%d", &weight[i][j]);
    //fclose(f);

    /* Initialise d with infinity */
    for (i = 0; i < n; ++i)
        d[i] = 100000;

    /* Mark all nodes as NOT beeing in the minimum spanning tree */
    for (i = 0; i < n; ++i)
        inTree[i] = 0;

    /* Add the first node to the tree */
    printf("Adding node %c\n", 0 + 'A');
    inTree[0] = 1;
    updateDistances(0, n);

    int total = 0;
    int treeSize;
    for (treeSize = 1; treeSize < n; ++treeSize) {
        /* Find the node with the smallest distance to the tree */
        int min = -1;
        for (i = 0; i < n; ++i)
            if (!inTree[i])
                if ((min == -1) || (d[min] > d[i]))
                    min = i;

        /* And add it */
        printf("Adding edge %c-%c\n", whoTo[min] + 'A', min + 'A');
        inTree[min] = 1;
        total += d[min];

        updateDistances(min, n);
    }

    printf("Total distance: %d\n", total);

    return 0;
}
