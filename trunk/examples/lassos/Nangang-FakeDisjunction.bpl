//#rTermination
/* Program that look very difficult but whose termination is surprisingly easy
 * to prove.
 * We received this program from Ondra Lengál and Yu-Fang Chen.
 * 
 * 
 * In a setting where we consider the program as a loop with two branches
 * (i.e., no large block encoding) Ultimate Büchi Automizer can prove
 * termination.
 * Ultimate Büchi Automzier decomposes the program into two modules for which
 * the ranking functions are f(i,j)=i and f(i,j)=j.
 * The first module represents all program traces that take the if-branch 
 * infinitely often. The second module represents all program traces that 
 * take the if-branch infinitely often.
 * This works (perhaps surprisingly) because for the first set of traces
 * we have that i>j holds (condition of if-branch) and hence the second
 * disjunct of the while loop's condition implies the first disjunct.
 * However, it seems that we only succeed because we obtain the (simple)
 * ranking function f(i,j)=i. Currently, I presume that we would fail if
 * we would obtain the ranking function f(i,j)=i-j.
 * 
 * 
 * In a setting where we consider the program as loop with a single code block
 * that condenses both branches the program consists only of a single infinite
 * trace. Hence, in our tool the burden of proving termination is completely
 * shiftend to the Ultimate LassoRanker.
 * Ultimate LassoRanker can find the 2-parallel ranking function
 * f = max{0, 4*main_i + 1} + max{0, 2*main_j + 1}.
 * The definition of a parallel ranking function can be found in Section 4.5
 * of our LMCS article.
 * http://www.lmcs-online.org/ojs/viewarticle.php?id=1739
 *
 * 
 * 
 * Date: 2017-07-14
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
  var i, j: int;
  while (i >= 0 || j >= 0) {
    if (i > j) {
      i := i - 1;
    } else {
      j := j - 1;
	}
  }
}

