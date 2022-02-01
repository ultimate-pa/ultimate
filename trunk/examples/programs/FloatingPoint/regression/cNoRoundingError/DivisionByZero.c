//#Safe
/*
 * For floating types, the division by zero is legal in C
 * However, Ultimate has a setting to check for division by zero
 * of floating types.
 * 
 * Date: 2017-03-26
 * Author: Matthias Heizmann
 */


int main()
{
  double x = 2.0;
  double y = x / 0.0;
  return 0;
}
