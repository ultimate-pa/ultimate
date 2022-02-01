//#Safe
/* Date: 2017-05-02
 * Author: dietsch@informatik.uni-freiburg.de
 *
 * 
 * Leads to StackOverflow in LA Woelfing (getIteratedSymbolicMemoryForLoop)
 * The procedure call is necessary 
 */

procedure ULTIMATE.start() returns (){
    call main();
}

procedure main() returns (){
    while (true)
    {
        if (false) {
            break;
        }
        while (true)
        {
            
        }
    }
}

