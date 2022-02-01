/*
-------------------------------------------------------------------------
cube.c
-------------------------------------------------------------------------
This program will generate a given number of points uniformly distributed
inside a cube. The number of points is given on the command line as the
first parameter.  Thus `cube 100' will generate 100 points in a cube,
and output them to stdout.
        A number of different command-line flags are provided to set the
side-length of the cube, control the output format, or to change the cube
to a box. The definition of the flags is printed if the program is
run without arguments: `cube'.  Note that -s sets the half-side
length: points are generated between -s and +s.
        The default output is integers, rounded from the floating point
computation.  The rounding implies that some points will fall outside
the sphere, and some inside.  If all are required to be inside, then
the calls to irint() should be removed.
        The flags -a, -b, -c are used to set different x, y, z side-lengths
for a box.  Note that the points are not uniformly distributed: they are
uniformly distributed on the cube and then scaled.
        random() is used to generate random numbers, seeded with time().
How to compile:
        gcc -o cube cube.c -lm

Written by Joseph O'Rourke and Min Xu, June 1997.
Used in the textbook, "Computational Geometry in C."
Questions to orourke@cs.smith.edu.
--------------------------------------------------------------------
This code is Copyright 1997 by Joseph O'Rourke.  It may be freely
redistributed in its entirety provided that this copyright notice is
not removed.
--------------------------------------------------------------------
*/
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <time.h>

/* MAX_INT is the range of random(): 2^{31}-1 */
#define MAX_INT   2147483647
#define TRUE      1
#define FALSE     0

#define irint(x) ((int)rint(x))

void print_instruct( void )
{
  printf ( "Please enter your input according to the following format:\n" );
  printf ( "\tcube [number of points] [-flag letter][parameter value]\n" );
  printf ( "\t\t (no space between flag letter and parameter value!)\n" );
  printf ( "Available flags are:\n" );
  printf ( "\t-s[parameter] \t half side-length of the cube (default: +/-100)\n" );
  printf ( "\t-f            \t set output to floating point format (default: integer)\n");
  printf ( "\t-a[parameter] \t x-axis length (default: s)\n");
  printf ( "\t-b[parameter] \t y-axis length (default: s)\n");
  printf ( "\t-c[parameter] \t z-axis length (default: s)\n");
}

void TestFlags (int argc, char *argv[], int *s1, int *s2, int *s3, int *s, int *float_pt)
{

  int i = 2;

  /* Test for flags */
  while ( i < argc ) {

    /* Test for side-length flag */
    if ( strncmp ( argv[i], "-s", 2 ) == 0 ) {
      if ( sscanf( &argv[i][2], "%d", s ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);
      else if (*s == 0 )
        printf ( "Invalid side-length flag\n" ),
        exit (1);
      else
        *s1 = *s2 = *s3 = *s;
    }

    /* Test whether user wants floating point output */
    if ( strncmp ( argv[i], "-f", 2 ) == 0 )
      *float_pt = TRUE;

    /* Test for x, y, z dimensions if any */
    if ( strncmp ( argv[i], "-a", 2 ) == 0 )
      if ( sscanf ( &argv[i][2], "%d", s1 ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);
    if ( strncmp ( argv[i], "-b", 2 ) == 0 )
      if ( sscanf ( &argv[i][2], "%d", s2 ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);
    if ( strncmp ( argv[i], "-c", 2 ) == 0 )
      if ( sscanf ( &argv[i][2], "%d", s3 ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);

    i++;
  }

  if ( *s1 == 0 || *s2 == 0 || *s3 == 0 )
    printf ( "Invalid axis length\n" ),
    exit (1);
}

int main( argc, argv )
int argc;
char *argv[];
{
  int n;                /* number of points */
  double x, y, z;
  double S = 100.0;     /* default (half) side-length */
  int s;                /* true (half) side-length */
  int s1, s2, s3;       /* axis lengths */
  int float_pt = FALSE;

  srandom( (int) time((long *) 0 ) );
  if ( argc < 2 )
    print_instruct(),
    exit (1);

  s = S;
  s1 = s2 = s3 = s;
  TestFlags ( argc, argv, &s1, &s2, &s3, &s, &float_pt );

  n = atoi( argv[1] );

  while (n > 0) {
    /* Generate a random point on a unit cube. */
    x = 2.0 * (double) random() / MAX_INT - 1.0;
    y = 2.0 * (double) random() / MAX_INT - 1.0;
    z = 2.0 * (double) random() / MAX_INT - 1.0;


    if ( float_pt == FALSE )
      printf ( "%6d  %6d  %6d\n",
                irint( s1 * x ),
                irint( s2 * y ),
                irint( s3 * z ) );
    else
      printf ( "%6f  %6f  %6f\n", s1 * x, s2 * y, s3 * z );

    n--;
  }
  return 0;
}
