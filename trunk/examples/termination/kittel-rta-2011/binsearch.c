#define maxN 1000

struct node
{
    int key;
    int info;
};

int N;

struct node a[maxN + 1];

int binsearch(int v)
{
    int l = 1;
    int r = N;
    int x;
    while (r >= l) {
        x = (l + r) / 2;
        if (v < a[x].key) {
            r = x - 1;
        } else {
            l = x + 1;
        }
        if (v == a[x].key) {
            return a[x].info;
        }
    }
    return -1;
}
