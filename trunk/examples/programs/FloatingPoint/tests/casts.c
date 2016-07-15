//#Safe
/*
 * Date: April 2016
 * Author: Maximilian Rohland
 *
 * float casts
 */
int main()
{
  double x = 3.1414141232192;
  float y = 4.321324f;
  long double z = 2.5456786543456l;

  int a = (int) x;
  float b = (float) x;
  long double c = (long double) x;
  float d = (float) z;
  double e = (double) y;
  double f = (double) z;
  long double g = (long double) y;
  float h = (float) e;
  long i = (long) x;
  long long j = (long long) z;

  if (y != h)
  {
    //@assert \false;
  }

  return 0;
}
