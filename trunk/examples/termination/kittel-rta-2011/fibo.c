/*
  FIBO.C
  ======
  (c) Copyright Paul Griffiths 2000
  Email: mail@paulgriffiths.net

  Finds the first 'n' numbers in the Fibonacci sequence.
  'n' must be supplied as the sole command line argument,
  and must be between 3 and 47.
*/


#include <stdio.h>
#include <stdlib.h>


int ParseCmdLine(int argc, char *argv[]);

int main(int argc, char * argv[]) {
    unsigned long f1 = 1, f2 = 1;
    int temp, i = 3;
    int n = ParseCmdLine(argc, argv);

    printf("First %d numbers in the Fibonacci sequence:\n\n", n);

    printf("%11lu%11lu", f1, f2);

    for ( i = 3; i <= n; ++i ) {
        temp = f2;
        f2 += f1;
        f1 = temp;

        printf("%11lu", f2);

        if ( i % 5 == 0 )
            putchar('\n');
    }
    putchar('\n');

    return EXIT_SUCCESS;
}


/*  Returns the integer specified on the command line  */

int ParseCmdLine(int argc, char *argv[]) {
    int n;
    char * endptr;

    if ( argc < 2 ) {
        fprintf(stderr, "You must supply an argument\n");
        exit(EXIT_FAILURE);
    }
    else if ( argc > 2 ) {
        fprintf(stderr, "You must only supply one argument\n");
        exit(EXIT_FAILURE);
    }

    n = strtol(argv[1], &endptr, 0);
    if ( *endptr ) {
        fprintf(stderr, "You must supply a whole number as an argument\n");
        exit(EXIT_FAILURE);
    }

    if ( n < 3 ) {
        fprintf(stderr, "You must supply a number greater than 2\n");
        exit(EXIT_FAILURE);
    }
    else if ( n > 47 ) {
        fprintf(stderr, "You must supply a number less than 48\n");
        exit(EXIT_FAILURE);
    }
 
    return n;
}
