//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 16.05.2011
 *
 * Concurrent program which implements a mutual exclusion algorithm.
 * Translated (by hand) to a interprocedural program using the
 * transformation I investigated in Bangalore.
 */

 var pc : int;

 var lock1 : int;
 var lock2 : int;
 
 var ressource1 : int;
 var ressource2 : int;



procedure Thread1();
modifies pc, lock1, lock2, ressource1, ressource2;

implementation Thread1()
{
  ressource1 := 0;
  ressource2 := 0;
  
  lock1 := 0;
  lock2 := 0;
  pc := 0;
  
  safe:
  while (true) {
    if (*) {call Thread2();}
    if (*) {goto aquireRes1;}
    if (*) {goto aquireRes2;}
  }
  
  aquireRes1:
  if (*) {call Thread2();}
  assume (lock1 == 0);
  lock1 := 1;
  goto critRes1;
  
  critRes1:
  if (*) {call Thread2();}
  assert (ressource1 == 0);
  ressource1 := 1;
  goto releaseRes1;
  
  releaseRes1:
  if (*) {call Thread2();}
  ressource1 := 0;
  lock1 := 0;
  goto safe;
  
  
  aquireRes2:
  if (*) {call Thread2();}
  assume (lock2 == 0);
  lock2 := 1;
  goto critRes2;
  
  critRes2:
  if (*) {call Thread2();}
  assert (ressource2 == 0);
  ressource2 := 1;
  goto releaseRes2;
  
  releaseRes2:
  if (*) {call Thread2();}
  ressource2 := 0;
  lock2 := 0;
  goto safe;


}





procedure Thread2();
modifies pc, lock1, lock2, ressource1, ressource2;


implementation Thread2()
{
  if (pc == 0) { goto safe; }
  if (pc == 11) { goto aquireRes1; }
  if (pc == 12) { goto critRes1; }
  if (pc == 13) { goto releaseRes1; }
  if (pc == 21) { goto aquireRes2; }
  if (pc == 22) { goto critRes2; }
  if (pc == 23) { goto releaseRes2; }
  
  safe:
  while (true) {
    if (*) { pc := 0; return; }
    if(*) {goto aquireRes1;}
    if(*) {goto aquireRes2;}
  }
  
  aquireRes1:
  if (*) { pc := 11; return; }
  assume (lock1 == 0);
  lock1 := 2;
  goto critRes1;
  
  critRes1:
  if (*) { pc := 12; return; }
//  assert (ressource1 == 0);
  ressource1 := 1;
  goto releaseRes1;
  
  releaseRes1:
  if (*) { pc := 13; return; }
  ressource1 := 0;
  lock1 := 0;
  goto safe;
  
  
  aquireRes2:
  if (*) { pc := 21; return; }
  assume (lock2 == 0);
  lock2 := 2;
  goto critRes2;
  
  critRes2:
  if (*) { pc := 22; return; }
//  assert (ressource2 == 0);
  ressource2 := 1;
  goto releaseRes2;
  
  releaseRes2:
  if (*) { pc := 23; return; }
  ressource2 := 0;
  lock2 := 0;
  goto safe;
  
  
}

