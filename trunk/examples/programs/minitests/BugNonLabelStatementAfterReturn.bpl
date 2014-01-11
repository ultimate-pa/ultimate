// #Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 10.8.2012
 * 
 * Bug in r6669. RCFGBuilder crashed if thre is a non-label statement after a
 * return.
 * 
 */

procedure proc() returns (#res:int);
    modifies ;

implementation proc() returns (#res:int)
{
    #res := 1;
    return;
    assume true;
  switch_1_break:
}
