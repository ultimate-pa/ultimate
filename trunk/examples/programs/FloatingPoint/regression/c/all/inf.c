//#Safe
/* 
 * Author: dietsch@cs.uni-freiburg.de
 * Date: 2020-04-23
 * 
 */

#include <stdio.h>
#include <float.h>
#include <math.h>

int main()
{
  int zero=0;
  
  if (sizeof ((__builtin_inff())/zero) == sizeof (float))
  {
    if(!__isinff ((__builtin_inff())/zero))
    {
      //@ assert \false;
    }
  }
  else if (sizeof ((__builtin_inff())/zero) == sizeof (double))
  {
    if(!__isinf ((__builtin_inff())/zero))
    {
      //@ assert \false;
    }
  }
  else
  {
    if(!__isinfl ((__builtin_inff())/zero))
    {
      //@ assert \false;
    }
  }
}

