/* An example using integer division, given to me by Aviad Pineles
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */
extern int __VERIFIER_nondet_int(void);


 int f(int a) {
    int tmp, count = 0;
    while(a > 1) {
      tmp = a % 2;
      if(tmp == 0) a = a / 2;
      else a = a - 1;
      count++;
    }
    return count;
  }
  
int main() {
    int x = __VERIFIER_nondet_int();
    int count = f(x);
    return count;
  }

