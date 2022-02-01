// #Safe
/*
 * If we extend the SequentialComposition to Calls without considering
 * the "oldVar assignments" large block encoding is unsound.
 * The call of procedure callMe is summarized to one CodeBlock whose
 * TransFormula states that old(g)=20. However, in the context of main
 * old(g)=20 is not established by calling callMe.
 * 
 * Note that the while loop in main was only introduced to prevent summarizing
 * the call of main in ULTIMATE.start().
 * 
 * Note that ULTIMATE.start() is only necessary as long as we do not fix the
 * "precondition bug" (precondition of each trace is true and not old(g)=g for
 * each global g)
 * 
 * Date: 20.02.2013
 * Author: Stefan Wissert and heizmann@informatik.uni-freiburg.de
 */


var g : int;


procedure ULTIMATE.start() returns ();
modifies g;

implementation ULTIMATE.start() returns ()
{
  g := 1;
  call main();
  return;
}


procedure main() returns ();
  requires g == 1;
  modifies g;
  ensures old(g) == 1;

implementation main() returns ()
{
  var i : int;
  g := 20;
  while(*) {
    i := 0;
  }
  call callMe();
  return;
}


procedure callMe() returns ();
  requires g == 20;
  modifies g;
  ensures old(g) == 20;

implementation callMe() returns ()
{
    return;
}

