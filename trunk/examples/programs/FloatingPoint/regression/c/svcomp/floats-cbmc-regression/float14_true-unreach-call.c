#include <math.h>
extern void __VERIFIER_error(void);
int main()
{
  float temp;
  
  temp = 1.8e307f + 1.5e50f;	// should produce overflow -> +infinity (according to standard)
  if(!(isinf(temp))) __VERIFIER_error();
  
  float x;
  
  x=temp-temp;
  
  // should be +inf
  if(!(isinf(temp))) __VERIFIER_error();
}
