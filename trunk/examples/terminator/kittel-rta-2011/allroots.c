#include <stdio.h>
#include <stdlib.h>
#include <math.h>

double newton (int N,double P[],double A,double B);

double DERIV_X;      /* Global Var: HORNERS function has the side effect
                        of setting DERIV_X to the derivative of polynomial
                        at X */
double HORNERS(int DEGREE,double COEF[],double X);
double d_abs(double D);

/* tollerance of stopping criteron */
#define Episolon_n        0.5E-5
#define Episolon_b        0.5E-1
#define Episolon_sec      0.5E-5
#define MAX_1             40

#define Increment         0.49E-1

extern void allroots(int No,double Po[],int N,double Pn[]);
extern void deflat(int No,double Po[],int N,double Pn[],double ROOT);

int main(void) {
  static double A[] = {4.1,-3.9,-1.0,1.0};
  int N = 3;
  int J;
  printf("DEBUG: %g %g\n",2.69065*2.69065*2.69065,2.69065*2.69065);
  printf("==============================================================\n");
  printf("Find all roots of\n");

  for (J=N;J>0;J--) {
    printf("%g",d_abs(A[J]));
    if (A[J-1] < 0)
      printf("x**%d - ",J);
    else
      printf("x**%d + ",J);
  }

  printf("%g\n",d_abs(A[0]));
  printf("using NEWTON method.\n");
  printf("==============================================================\n");
  allroots(N,A,N,A);
  return 0;
}

void allroots(int No,double Po[],int N,double Pn[])

/* Computes the Maximum interval that all the roots for the polynomial P
   can contain with |root| < |P[0]| + |P[1]| + ... + |P[n]| \ |P[n]| where
   P[i] is the coefficent of the Ith degree of the polynomial

   Next it looks for a change of sign of F(x) on the range, when it finds one
   it calls a METHOD for finding an individual root and then repeats the
   process with the range now starting just after the last found root */

{
  int I;              /* counter */
  double ROOT;

  double LOWER,UPPER; /* lower and upperbound of all roots of P */

  UPPER = 0;
  for (I=0;I<=N;I++)
    UPPER += d_abs(Pn[I]);

  UPPER /= d_abs(Pn[N]);
  LOWER = -UPPER - 1.0;

  if (N <= 0)
    printf("No roots\n");
  else
    if (N == 1) {
      ROOT = -Pn[0]/Pn[1];
      printf("   ROOT = %g\n",ROOT);
    }
    else
      if (N == 2) {
        ROOT = (-Pn[1] + sqrt(Pn[1]*Pn[1] - 4*Pn[2]*Pn[0]))/(2*Pn[2]);
        printf("  ROOT = %g (from quadratic formula)\n",ROOT);
        ROOT = (-Pn[1] - sqrt(Pn[1]*Pn[1] - 4*Pn[2]*Pn[0]))/(2*Pn[2]);
        printf("  ROOT = %g (from quadratic formula)\n",ROOT);
      }
      else {
        ROOT = newton(N,Pn,LOWER,UPPER);
        deflat(No,Po,N,Pn,ROOT);
      }
}


void deflat(int No,double Po[],int N,double Pn[],double ROOT)
{
  double *TP;
  int I,J;

  if (N != No) {
    printf("----> Refine Root on the Orginal Polynomial (non-deflated)\n");
    newton(No,Po,ROOT-.5,ROOT+.5);
  }

  TP = (double *) calloc(N,sizeof(ROOT));

  TP[N-1]=Pn[N];
  for (I=N-2;I>=0;I--)
    TP[I] = TP[I+1]*ROOT+Pn[I+1];

  for (J=N;J>0;J--) {
    printf("%g",d_abs(Pn[J]));
    if (Pn[J-1] < 0)
      printf("x**%d - ",J);
    else
      printf("x**%d + ",J);
  }

  printf("%g\n",d_abs(Pn[0]));
  printf("     DEFLATED to\n(x - %g)*(",ROOT);

  for (J=N-1;J>0;J--) {
    printf("%g",d_abs(TP[J]));
    if (TP[J-1] < 0)
      printf("x**%d - ",J);
    else
      printf("x**%d + ",J);
  }

  printf("%g)\n",d_abs(TP[0]));

  if (N == 3) {
    ROOT = (-TP[1] + sqrt(TP[1]*TP[1] - 4*TP[2]*TP[0]))/(2*TP[2]);
    printf("\n  ROOT = %g (from quadratic formula)\n",ROOT);
    printf("----> Refine Root on the Orginal Polynomial (non-deflated)\n");
    newton(No,Po,ROOT-.5,ROOT+.5);

    ROOT = (-TP[1] - sqrt(TP[1]*TP[1] - 4*TP[2]*TP[0]))/(2*TP[2]);
    printf("  ROOT = %g (from quadratic formula)\n",ROOT);
    printf("----> Refine Root on the Orginal Polynomial (non-deflated)\n");
    newton(No,Po,ROOT-.5,ROOT+.5);
  }
  else {
    allroots(No,Po,N-1,TP);
  }
  free(TP);
}

double newton (int N,double P[],double A,double B)
{
  double T_DOUBLE;    /* for temporary storage */
  double Xk,Xk1;      /* the kth and k+1rst quess at the root */
  int K = 0;          /* number of iterations so far */

/* make sure that A is lower bound of the interval and B is the upper bound */
  if (B < A) {
    T_DOUBLE = A;
    A = B;
    B = T_DOUBLE;
  }

  printf("     NEWTON Called on interval [%g,%g]\n",A,B);
  Xk  = A;
  Xk1 = (A + B)/2;     /* initial quess is the midpoint of the interval */

  while ( (d_abs(Xk1-Xk)/d_abs(Xk1) > Episolon_n) && K <= MAX_1 ) {
    printf("     X[%d] = %g\n",K+1,Xk1);
    Xk = Xk1;
    Xk1 = Xk1 - HORNERS(N,P,Xk1)/DERIV_X;
    K ++;
  }
  printf("ROOT: %g (approx.)\n\n",Xk1);
  return Xk1;
}

double DERIV_X;

double HORNERS(int DEGREE,double COEF[],double X)

/* Algo. 2.6 (pp. 68 - 69) of NUMERICAL ANALYSIS by Richard Burden and
   J. Douglas Faires */
{
  double P_X;        /* Value of the polynomial at X */
  double dP_X;       /* Value of the derivative of the polynomial at X */
  int J;             /* a counter variable */

  P_X = dP_X = COEF[DEGREE];

  for (J = DEGREE - 1; J >= 1; J --) {
    P_X = X*P_X + COEF[J];
    dP_X = X*dP_X + P_X;
  }

  P_X = X*P_X + COEF[0];

  DERIV_X = dP_X;
  return P_X;
}

double d_abs(double D)
{
  if (D < 0) D = -1.0*D;
  return D;
}
