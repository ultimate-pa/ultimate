#include <limits.h>

struct point { int x, y; char c; };
struct line { struct point p1, p2; };

int ccw(struct point p0, struct point p1, struct point p2)
{
    int dx1, dx2, dy1, dy2;
    dx1 = p1.x - p0.x;
    dy1 = p1.y - p0.y;
    dx2 = p2.x - p0.x;
    dy2 = p2.y - p0.y;
    if (dx1*dy2 > dy1*dx2) return +1;
    if (dx1*dy2 < dy1*dx2) return -1;
    if ((dx1*dx2 < 0) || (dy1*dy2 < 0)) return -1;
    if ((dx1*dx1+dy1*dy1) < (dx2*dx2+dy2*dy2)) return +1;
    return 0;
}

int intersect(struct line l1, struct line l2)
{
    return ((ccw(l1.p1, l1.p2, l2.p1)
            *ccw(l1.p1, l1.p2, l2.p2)) <= 0)
        && ((ccw(l2.p1, l2.p2, l1.p1)
            *ccw(l2.p1, l2.p2, l1.p2)) <= 0);
}

int inside(struct point t, struct point p[], int N)
{
    int i, count = 0, j = 0;
    struct line lt,lp;
    p[0] = p[N]; p[N+1] = p[1];
    lt.p1 = t; lt.p2 = t; lt.p2.x = INT_MAX;
    for (i = 1; i <= N; i++)
    {
        lp.p1 = p[i]; lp.p2 = p[i];
        if (!intersect(lp, lt))
        {
            lp.p2 = p[j]; j = i;
            if (intersect(lp, lt)) count++;
        }
    }
    return count & 1;
}
