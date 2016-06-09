/*
 * Date: April 2016
 * Author: Maximilian Rohland
 *
 * float comparisons
 */

int main()
{
  float x = 1.2f;
  float y = 1.2f;
  float z = 1.3f;
  double a = 1.5;
  double b = 1.5;

  if (x != y) {
    //@assert \false;
  }

  if ( a != b) {
    //@assert \false;
  }

  if (x == a) {
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
