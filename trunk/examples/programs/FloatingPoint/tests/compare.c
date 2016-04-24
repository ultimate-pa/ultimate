/*
 * Date: April 2016
 * Author: Maximilian Rohland
 *
 * float comparisons
 */

int main()
{
  double x = 1.2;
  double y = 1.2;
  double z = 1.3;

  if (x != y) {
    //@assert \false;
  }
  if (x == z) {
    //@assert \false;
  }
  if (x > z) {
    //@assert \false;
  }
  if (x >= z) {
    //@assert \false;
  }
  if (z < x) {
    //@assert \false;
  }
  if (z <= x) {
    //@assert \false;
  }

  return 0;
}
