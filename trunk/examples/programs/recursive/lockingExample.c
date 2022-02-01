//#Safe

/* Precedural version of the "Locking Example" which occurs in e.g.
 *
 * Thomas A. Henzinger, Ranjit Jhala, Rupak Majumdar, Grégoire Sutre: Lazy abstraction. POPL 2002
 * Kenneth L. McMillan: Lazy Abstraction with Interpolants. CAV 2006
 *
 * The program is correct with respect to the requires clauses of lock and unlock.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 13.8.2010
 */

int locked;

/*@ requires locked == 0;
  @*/
void lock();

void lock() {
  locked = 1;
}


/*@ requires locked == 1;
  @*/
void unlock();

void unlock() {
  locked = 0;
}


/*@ requires locked == 0;
  @*/
int main();

int main() {
    int new, auld;
  
    while (1) {
        lock();
        auld = new;
        int nondet;
        if (nondet) {
            unlock();
            new = new + 1;
        }
        if (new == auld) {
            break;
        }
    } 
}
