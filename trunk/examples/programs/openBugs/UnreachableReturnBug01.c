//???safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-16
 * 
 * AssertionError: unreachable return
 *  at de.uni_freiburg.informatik.ultimate.automata.nestedword.DownStateConsistencyCheck.checkIfEachDownStateIsJustified(DownStateConsistencyCheck.java:142)]
 * 
 * settings/svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Default.epf
 * toolchains/AutomizerC.xml
 * 
 */



int fibo1(int n) {
    if (n < 1) ; else if (0) ; else {
        return fibo2(n-1) + fibo2(n  );
    }
}

int fibo2(int n) {
                       
        return     fibo1(n-2);
     
}

void main( ) {
    int x = 8;
      fibo1(x);
          
        ERROR: __VERIFIER_error();

}
