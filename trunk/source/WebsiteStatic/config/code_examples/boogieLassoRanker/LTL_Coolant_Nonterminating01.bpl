//#rNonTermination
/* Example that we obtained from checking LTL properties for coolant example.
 * 
 * Date: 2015-01-14
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */


procedure main()
{
  var ~time, ~tempIn, ~temp, ~limit, ~chainBroken, #t~nondet0: int;

  ~time := 0;
  ~tempIn := 0; 
  ~temp := 0;
  ~limit := 5; 
  ~chainBroken := 0; 
  assume true;
  
  LoopEntry:
  assume true;
  assume !(~chainBroken == 1); 
  assume !!true;
  assume !(~chainBroken == 1); 
  ~time := ~time + 1;
  assume !(~chainBroken == 1);
  ~tempIn := #t~nondet0;
  assume !(~chainBroken == 1); 
  havoc #t~nondet0;
  assume !(~chainBroken == 1); 
  ~temp := ~tempIn - 273;
  assume !(~chainBroken == 1); 
  assume !(~temp > ~limit);
  assume !(~chainBroken == 1);
  goto LoopEntry;
  
}
