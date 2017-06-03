//#Safe
/*
 *
 * Date: April 2016
 * Author: Maximilian Rohland
 *
 * float arithmetics
 */


int main()
{
  double x = 2.0;
  double y = 1.0;
  double z = x + y;
  double a = 3.0;

  if (z != a) {
    //@assert \false;
  } 

  if ((x - y) != 1.0) {
    //@assert \false;
  }

  return 0;
}
