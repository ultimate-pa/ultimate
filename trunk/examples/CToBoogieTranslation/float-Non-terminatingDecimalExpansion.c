//#Safe 
/*
 * Author: dietsch@informatik.uni-freiburg.de 
 * 
 * Example .c program for the following issue: 
 *  The division Imref/Iscref is not representable as BigDecimal (but as Rational).
 * 
 * > SyntaxErrorResult [Line: 226]: Incorrect Syntax
 * >     Non-terminating decimal expansion; no exact representable decimal result.
 * > RESULT: Ultimate could not prove your program: Incorrect Syntax
 * > 
 * > this 226 line has:      a = qkb*(Vmref-Vocref)/(N*Tk*logFUNC(1-Imref/Iscref));
 * > 
 * > a, qkb, Tk are float 
 * > 
 * > The other variable are define:
 * > #define Vocref 45.5
 * > #define Vmref 37
 * > #define N 72
 * > #define Iscref 9.34
 * > #define Imref 8.78
 * > 
 * > And logFUNC is a function that returns double
 * 
 */
 
#define Vocref 45.5
#define Vmref 37
#define N 72
#define Iscref 9.34
#define Imref 8.78

extern float __VERIFIER_nondet_float(void);
extern double __VERIFIER_nondet_double(void);

double logFUNC(int x){
  
  return __VERIFIER_nondet_double();
}

int main(){
  float qkb = __VERIFIER_nondet_float();
  float Tk = __VERIFIER_nondet_float();
  
  float a = qkb*(Vmref-Vocref)/(N*Tk*logFUNC(1-Imref/Iscref));
  return 0;
}