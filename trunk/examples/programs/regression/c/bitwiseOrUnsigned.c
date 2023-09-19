// #Unsafe
/*
 * https://github.com/ultimate-pa/ultimate/issues/646
 * The BitabsTranslation had a wrong assumption for unsigneds.
 * 
 * Date: 2023-09-19
 * Author: Novak756
 *
 */

extern void __VERIFIER_error(void);
extern unsigned char __VERIFIER_nondet_uchar(void);

int main(){
  unsigned char c = __VERIFIER_nondet_uchar();
  if(!((((unsigned int) (((int) ((int) ((int)((c) - (48))) >> (int) ((unsigned int)(31))) >> (int) ((unsigned int)(31))) + ((int) ((int) ((int)((c) - (48))) >> (int) ((unsigned int)(31))) >> (int) ((unsigned int)(31))))) | ((int) (((unsigned int) (((int) ((int)((c) - (48))) >> (int) ((unsigned int)(31))) + ((int) ((int)((c) - (48))) >> (int) ((unsigned int)(31))))) | ((int) ((unsigned int) (((int)((c) - (48))) + ((int)((c) - (48))))) >> (int) ((unsigned int)(31)))) >> (int) ((unsigned int)(31)))) == ((unsigned int) 0))){
    __VERIFIER_error();
  }
  return 0;
}
