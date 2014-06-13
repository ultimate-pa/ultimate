#include <stdio.h>

#define NMAX 1001

int nondef(void);

int main()
{
    int x[NMAX],y[NMAX],z[NMAX];/* input points xy,z=x^2+y^2 */
    int n;                      /* number of input points */
    int i, j, k, m;             /* indices of four points */
    int xn, yn, zn;             /* outward vector normal to (i,j,k) */
    int flag;                   /* t if m above of (i,j,k) */
    int F = 0;                  /* # of lower faces */

    /* Input points and compute z = x^2 + y^2. */
    //scanf("%d", &n);
    n = nondef();
    for ( i = 0; i < n; i++ ) {
        scanf("%d %d", &x[i], &y[i]);
        z[i] = x[i] * x[i] + y[i] * y[i];
    }

    /* For each triple (i,j,k) */
    for ( i = 0; i < n - 2; i++ )
      for ( j = i + 1; j < n; j++ )
            for ( k = i + 1; k < n; k++ )
                if ( j != k ) {
                    /* Compute normal to triangle (i,j,k). */
                    xn = (y[j]-y[i])*(z[k]-z[i]) - (y[k]-y[i])*(z[j]-z[i]);
                    yn = (x[k]-x[i])*(z[j]-z[i]) - (x[j]-x[i])*(z[k]-z[i]);
                    zn = (x[j]-x[i])*(y[k]-y[i]) - (x[k]-x[i])*(y[j]-y[i]);

                    /* Only examine faces on bottom of paraboloid: zn < 0. */
                    if ( zn < 0 ) {
                        flag = 1;
                        /* For each other point m */
                        for (m = 0; m < n; m++)
                            /* Check if m above (i,j,k). */
                            flag = flag && ((x[m]-x[i])*xn + (y[m]-y[i])*yn + (z[m]-z[i])*zn <= 0);
                    }
                    if (flag) {
                        printf("z=%10d; lower face indices: %d, %d, %d\n", zn, i, j, k);
                        F++;
                    }
                }
    printf("A total of %d lower faces found.\n", F);
    return 0;
}
