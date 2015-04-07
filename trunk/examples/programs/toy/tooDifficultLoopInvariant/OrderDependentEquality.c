//#Safe
/**
 * Author: Daniel Dietsch
 * Date: 2015-04-07
 * 
 * In revision 13917 we are unable to prove correctness with the default settings.
 * If we move z=x two lines downwards we are able to prove correctness.
 * 
 * Betims "large constants late" heuristic crashes with the following error message.
 * java.lang.UnsupportedOperationException: ConstantTerm is neither BigInter nor BigDecimal, therefore comparison is not possible!
 */
extern int __VERIFIER_nondet_int(void);

int main(){
    int x=0;
    int y=0;
    int z=0;
    while(x<100){
        if(__VERIFIER_nondet_int()){
            y++;
        } else {
            y--;
        }
        z=x;
        x++;
        z++;
     }
    //@ assert (z==x); 
}