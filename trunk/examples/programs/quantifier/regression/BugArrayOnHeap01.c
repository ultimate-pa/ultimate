//#Safe
/*
 * In SVCOMP2014 we say (incorrectly) that this program is unsound.
 * We go to the error location with the following assume
 * assume !(#sizeof~INT + (~string_A~2.offset + 0 * #sizeof~CHAR) <= #length[~string_A~2.base]);
 * I don't know where this #sizeof~INT comes from, the remaining part seems reasonable.
 *
 * Date 3.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 */

int main()
{
  char string_A[5];
  string_A[0]='a';
}
