//#rNonTermination
/*
 * Date: 05.05.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Bug in r8726. Lasso ranker says:
 * Found linear ranking function 0.
 * 
 * Transition of while loop has no inVar, one outVar and this outVar does
 * not occur in the formula that describes the transition.
 */
var t : int;
procedure main() returns ()
modifies t;
{


    while (true)
    {
        havoc t;
        assume (t != 0);
        havoc t;
    }
}

