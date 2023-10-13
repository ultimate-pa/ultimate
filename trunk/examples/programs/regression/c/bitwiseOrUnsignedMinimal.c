// #Unsafe
/*
 * Minimal example for issue https://github.com/ultimate-pa/ultimate/issues/646
 * The BitabsTranslation had a wrong assumption for unsigneds.
 * 
 * Date: 2023-09-19
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

extern void __VERIFIER_error(void);

int main(){
  unsigned int left = (unsigned int) -1;
  unsigned int right = (unsigned int) 1;
	if (left | right != 0){
    __VERIFIER_error();
  }
  return 0;
}
