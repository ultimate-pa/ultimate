#include <stdio.h>
#define MAXROW     100
#define MAXCOL     100

int nondef(void);

float max(int len,float *p)
{
    float res;
    int i;

    res = p[0];
    for( i=1; i<len; i++ )
        if( p[i] > res )
            res = p[i];
    return res;
}


float sumEl(int nrRow,int nrCol,int maxCol,float *mat)
{
    int i, j;
    float sum;

    sum = 0.0;
    for( i=0; i<nrRow; i++ )
        for( j=0; j<nrCol; j++ )
            sum += mat[i*maxCol + j];

   return sum;
}


int main()
{
    int row, col, i, j;
    float add, maxRow, mat[MAXROW][MAXCOL];

    printf("\nInput nr. of rows and columns:");
    //scanf("%d %d", &row, &col);
    row = nondef();
    col = nondef();

    for( i=0; i<row; i++ )
        for( j=0; j<col; j++ ) {
            printf("Input element[%d,%d]:",i,j);
            scanf("%f", &mat[i][j] );
        }


    //calculates elements sum in matrix

    add=sumEl(row,col,MAXCOL,(float *) mat);
    printf("\n\nSum of matrix elements is %f", add );


    //prints maximal value of every mat. row 

    for(i=0;i<row;i++) {
        maxRow = max(col, &mat[i][0]);
        printf("\nBiggest element in row %d is %f\n",i,maxRow);
    }
    
    return 0;
}
