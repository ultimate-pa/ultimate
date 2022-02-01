/*
-------------------------------------------------------------------------
spiral.c
-------------------------------------------------------------------------
This program will generate a given number of spiral points uniformly
distributed on the surface of a sphere. The number of points is given on
the command line as the first parameter.  Thus `spiral 100' will generate
100 points on the surface of a sphere, and output them to stdout.
        A number of different command-line flags are provided to set the
radius of the sphere, control the output format, or generate points on
an ellipsoid.  The definition of the flags is printed if the program is
run without arguments: `spiral'.
        The idea behind the algorithm is that one can cut the globe with
N horizontal planes spaced 2/(N-1) units apart, forming N circles of
latitude on the sphere, each latitude containing one spiral point.  To
obtain the kth spiral point, one proceeds upward from the (k-1)st point
(theta(k-1), phi(k-1)) along a great circle to the next latitude and
travels counterclockwise along ti for a fixed distance to arrive at the
kth point (theta(k), phi(k)).
        The default output is integers, rounded from the floating point
computation.  The rounding implies that some points will fall outside
the sphere, and some inside.  If all are required to be inside, then
the calls to irint() should be removed.
        The flags -a, -b, -c are used to set ellipsoid axis lengths.
Note that the points are not uniformly distributed on the ellipsoid: they
are uniformly distributed on the sphere and that is scaled to an ellipsoid.
        random() is used to generate random numbers, seeded with time().
How to compile:
        gcc -o spiral spiral.c -lm

Reference: E.B. Saff and A.B.J. Kuijlaars, Distributing Many Points on a Sphere,
The Mathematical Intelligencer, 19(1), Winter (1997);

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

#define TRUE      1
#define FALSE     0

#define irint(x) ((int)rint(x))

void print_instruct( void )
{
  printf ( "Please enter your input according to the following format:\n" );
  printf ( "\tspiral [number of points] [-flag letter][parameter value]\n" );
  printf ( "\t\t (no space between flag letter and parameter value!)\n" );
  printf ( "Available flags are:\n" );
  printf ( "\t-r[parameter] \t set radius of the sphere (default: 100)\n" );
  printf ( "\t-f            \t set output to floating point format (default: integer)\n");
  printf ( "\t-a[parameter] \t ellipsoid x-axis length (default: sphere radius)\n");
  printf ( "\t-b[parameter] \t ellipsoid y-axis length (default: sphere radius)\n");
  printf ( "\t-c[parameter] \t ellipsoid z-axis length (default: sphere radius)\n");
}

void TestFlags (int argc, char *argv[], int *r1, int *r2, int *r3, int *r, int *float_pt)
{

  int temp = 2;

  /* Test for flags */
  while ( temp < argc ) {

    /* Test for radius flag */
    if ( strncmp ( argv[temp], "-r", 2 ) == 0 ) {
      if ( sscanf( &argv[temp][2], "%d", r ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);
      else if (*r == 0 )
        printf ( "Invalid radius flag\n" ),
        exit (1);
      else
        *r1 = *r2 = *r3 = *r;
    }

    /* Test whether user wants floating point output */
    if ( strncmp ( argv[temp], "-f", 2 ) == 0 )
      *float_pt = TRUE;

    /* Test for ellipsoid radius if any */
    if ( strncmp ( argv[temp], "-a", 2 ) == 0 )
      if ( sscanf ( &argv[temp][2], "%d", r1 ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);
    if ( strncmp ( argv[temp], "-b", 2 ) == 0 )
      if ( sscanf ( &argv[temp][2], "%d", r2 ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);
    if ( strncmp ( argv[temp], "-c", 2 ) == 0 )
      if ( sscanf ( &argv[temp][2], "%d", r3 ) != 1 )
        printf ( "No space between flag name and parameter, please!\n" ),
        exit (1);

    temp ++;
  }

  if ( *r1 == 0 || *r2 == 0 || *r3 == 0 )
    printf ( "Invalid ellipsoid radius\n" ),
    exit (1);
}


int main( argc, argv )
int argc;
char *argv[];
{
  int n;                /* number of points */
  int k;                /* index */
  double phi1, phi, theta, h, x, y, z;
  double R = 100.0;     /* default radius */
  int r;                /* true radius */
  int r1, r2, r3;       /* ellipsoid axis lengths */
  int float_pt = FALSE;

  if ( argc < 2 )
    print_instruct(),
    exit (1);

  r = R;
  r1 = r2 = r3 = r;
  TestFlags ( argc, argv, &r1, &r2, &r3, &r, &float_pt );

  n = atoi ( argv[1] );

  phi1 = 0.0;

  if ( float_pt == FALSE )
    printf ( "%6d  %6d  %6d\n", 0, 0, -1 * r3 );
  else
    printf ( "%6f  %6f  %6f\n", 0.0, 0.0, -1.0 * r3 );

  for ( k = 2; k <= n - 1; k ++ ) {
    /* Generate a random point on a sphere of radius 1. */
    h = -1 + 2 * ( k - 1 ) / ( double )( n - 1 );
    theta = acos ( h );

    if ( theta < 0 || theta > M_PI )
      printf( "Error\n" ),
      exit (1);

    phi = phi1 + 3.6 / ( sqrt ( ( double )n * ( 1 - h * h ) ) );
    phi = fmod ( phi, 2 * M_PI );
    phi1 = phi;

    x = cos ( phi ) * sin ( theta );
    y = sin ( phi ) * sin ( theta );
    /* z = cos ( theta ); But z==h, so: */
    z = h;

    if ( float_pt == FALSE )
      printf ( "%6d  %6d  %6d\n",
                irint( r1 * x ),
                irint( r2 * y ),
                irint( r3 * z ) );
    else
      printf ( "%6f  %6f  %6f\n", r1 * x, r2 * y, r3 * z );
  }

  if ( float_pt == FALSE )
    printf ( "%6d  %6d  %6d\n", 0, 0, 1 * r3 );
  else
    printf ( "%6f  %6f  %6f\n", 0.0, 0.0, 1.0 * r3 );

  return 0;
}
