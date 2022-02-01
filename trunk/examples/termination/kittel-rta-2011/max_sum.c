#include <stdio.h>

int MaxSubSumCubic( const int A[ ], int N )
{
    int ThisSum, MaxSum, i, j, k;

    MaxSum = 0;
    for( i = 0; i < N; i++ )
        for( j = i; j < N; j++ )
        {
            ThisSum = 0;
            for( k = i; k <= j; k++ )
                ThisSum += A[ k ];

            if( ThisSum > MaxSum )
                MaxSum = ThisSum;
        }
    return MaxSum;
}

int MaxSubSumQuadratic( const int A[ ], int N )
{
    int ThisSum, MaxSum, i, j;

    MaxSum = 0;
    for( i = 0; i < N; i++ )
    {
        ThisSum = 0;
        for( j = i; j < N; j++ )
        {
            ThisSum += A[ j ];

            if( ThisSum > MaxSum )
                MaxSum = ThisSum;
        }
    }
    return MaxSum;
}

int MaxSubSumLinear( const int A[ ], int N )
{
    int ThisSum, MaxSum, j;

    ThisSum = MaxSum = 0;
    for( j = 0; j < N; j++ )
    {
        ThisSum += A[ j ];

        if( ThisSum > MaxSum )
            MaxSum = ThisSum;
        else if( ThisSum < 0 )
            ThisSum = 0;
    }
    return MaxSum;
}

int main( )
{
    static int A[ ] = { 4, -3, 5, -2, -1, 2, 6, -2 };

    printf( "Maxsum = %d\n",
            MaxSubSumCubic( A, sizeof( A ) / sizeof( A[ 0 ] ) ) );
    printf( "Maxsum = %d\n",
            MaxSubSumQuadratic( A, sizeof( A ) / sizeof( A[ 0 ] ) ) );
    printf( "Maxsum = %d\n",
            MaxSubSumLinear( A, sizeof( A ) / sizeof( A[ 0 ] ) ) );

    return 0;
}
