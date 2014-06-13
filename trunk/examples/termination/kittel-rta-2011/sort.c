/* This file contains a collection of sorting routines */
#include <stdio.h>
#include <stdlib.h>

#define Error( Str )        FatalError( Str )
#define FatalError( Str )   fprintf( stderr, "%s\n", Str ), exit( 1 )

void assume(int);

typedef int ElementType;

void Swap( ElementType *Lhs, ElementType *Rhs )
{
    ElementType Tmp = *Lhs;
    *Lhs = *Rhs;
    *Rhs = Tmp;
}

void InsertionSort( ElementType A[ ], int N )
{
    int j, P;
    ElementType Tmp;

    for( P = 1; P < N; P++ )
    {
        Tmp = A[ P ];
        for( j = P; j > 0 && A[ j - 1 ] > Tmp; j-- )
            A[ j ] = A[ j - 1 ];
        A[ j ] = Tmp;
    }
}

void Shellsort( ElementType A[ ], int N )
{
    int i, j, Increment;
    ElementType Tmp;

    for( Increment = N / 2; Increment > 0; Increment /= 2 )
        for( i = Increment; i < N; i++ )
        {
            Tmp = A[ i ];
            for( j = i; j >= Increment; assume(Increment > 0), j -= Increment )
                if( Tmp < A[ j - Increment ] )
                    A[ j ] = A[ j - Increment ];
                else
                    break;
            A[ j ] = Tmp;
        }
}

#define LeftChild( i )  ( 2 * ( i ) + 1 )

void PercDown( ElementType A[ ], int i, int N )
{
    int Child;
    ElementType Tmp;

    for( Tmp = A[ i ]; LeftChild( i ) < N; i = Child )
    {
        assume (i >= 0);
        Child = LeftChild( i );
        if( Child != N - 1 && A[ Child + 1 ] > A[ Child ] )
            Child++;
        if( Tmp < A[ Child ] )
            A[ i ] = A[ Child ];
        else
            break;
    }
    A[ i ] =Tmp;
}

void Heapsort( ElementType A[ ], int N )
{
    int i;

    for( i = N / 2; i >= 0; i-- )  /* BuildHeap */
        PercDown( A, i, N );
    for( i = N - 1; i > 0; i-- )
    {
        Swap( &A[ 0 ], &A[ i ] );  /* DeleteMax */
        PercDown( A, 0, i );
    }
}

/* ROUTINES TO TEST THE SORTS */

void Permute( ElementType A[ ], int N )
{
    int i;

    for( i = 0; i < N; i++ )
        A[ i ] = i;
    for( i = 1; i < N; i++ )
        Swap( &A[ i ], &A[ rand( ) % ( i + 1 ) ] );
}

void Checksort( ElementType A[ ], int N )
{
    int i;
    for( i = 0; i < N; i++ )
        if( A[ i ] != i )
            printf( "Sort fails: %d %d\n", i, A[ i ] );
    printf( "Check completed\n" );
}

void Copy( ElementType Lhs[ ], const ElementType Rhs[ ], int N )
{
    int i;
    for( i = 0; i < N; i++ )
        Lhs[ i ] = Rhs[ i ];
}

#define MaxSize 7000
int Arr1[ MaxSize ];
int Arr2[ MaxSize ];

int main( )
{
    int i;

    for( i = 0; i < 10; i++ )
    {
        Permute( Arr2, MaxSize );
        Copy( Arr1, Arr2, MaxSize );
        InsertionSort( Arr1, MaxSize );
        Checksort( Arr1, MaxSize );

        Copy( Arr1, Arr2, MaxSize );
        Shellsort( Arr1, MaxSize );
        Checksort( Arr1, MaxSize );

        Copy( Arr1, Arr2, MaxSize );
        Heapsort( Arr1, MaxSize );
        Checksort( Arr1, MaxSize );
    }

    return 0;
}
