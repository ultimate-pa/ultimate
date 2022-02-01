//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 13.8.2010
 *
 * Precedural version of the "Locking Example" which occurs in e.g.
 *
 * Thomas A. Henzinger, Ranjit Jhala, Rupak Majumdar, Grégoire Sutre: Lazy abstraction. POPL 2002
 * Kenneth L. McMillan: Lazy Abstraction with Interpolants. CAV 2006
 *
 * The program is correct with respect to the requires clauses of lock and unlock.
 */

var lock: int;

procedure Main();
modifies lock;
requires lock ==0;


implementation Main()
{
  var new, auld: int;
  
  while (true) {
    call lock();
    auld := new;
    if (*) {
      call unlock();
      new := new + 1;
    }
    if (new == auld) {
      break;
    }
  } 
}


procedure lock();
modifies lock;
requires lock == 0;

implementation lock() {
  lock := 1;
}
 

procedure unlock();
modifies lock;
requires lock == 1;

implementation unlock() {
  lock := 0;
}
