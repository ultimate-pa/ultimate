/*
 * Author: hoenicke@informatik.uni-freiburg.de
 *
 * The PEA case study of an elevator from my PhD-thesis.
 *
 */

const Min : int;
const Max : int;


/* page 99: Translation of CSP part */
function {:inline true} cspinit (pc : int) returns (bool) { pc==0 }
function {:inline true} csptrans
  (pc : int, pc_p: int, newgoal : bool, start : bool, stop:bool, passed:bool) 
  returns (bool)
{
   (pc == pc_p            && !newgoal && !start && !stop && !passed)
   || (pc == 0 && pc_p==1 &&  newgoal && !start && !stop && !passed)
   || (pc == 1 && pc_p==2 && !newgoal &&  start && !stop && !passed)
   || (pc == 2 && pc_p==2 && !newgoal && !start && !stop &&  passed)
   || (pc == 2 && pc_p==0 && !newgoal && !start &&  stop && !passed)
}

/* page 102: Translation of Z part */
function {:inline true} zinit  (goal : int, current : int, dir : int) 
	 returns (bool) { goal == Min && current == Min && dir == Min }
function {:inline true} ztrans
  (goal : int, goal_p: int, current : int, current_p : int,
   dir : int, dir_p : int,
   newgoal : bool, start : bool, stop:bool, passed:bool) 
   returns (bool)
{
   (goal == goal_p && current == current_p && dir == dir_p
                          && !newgoal && !start && !stop && !passed)
   || (Min <= goal_p && goal_p <= Max && goal_p != current
                  && current == current_p && dir == dir_p
                          &&  newgoal && !start && !stop && !passed)
   || (goal == goal_p && current == current_p
                  && (goal > current ==> dir_p == 1)
                  && (goal < current ==> dir_p == -1)
                          && !newgoal &&  start && !stop && !passed)
   || (goal == current 
          && goal == goal_p && current == current_p && dir == dir_p
                          && !newgoal && !start &&  stop && !passed)
   || (goal == goal_p && current == current_p + dir && dir == dir_p
                          && !newgoal && !start && !stop &&  passed)
}


/* page 139 : Translation of DC part */
function {:inline true} dc1init(pc : int, c2:real, inc : real) returns (bool) 
   { pc == 0 && c2 == inc }
function {:inline true} dc1trans
   (pc : int, pc_p: int, c2: real, c2_p:real, inc:real, passed: bool)
   returns (bool)
{
   (pc == 0 && pc_p == 0 && c2_p == c2 + inc && !passed)
   || (pc == 1 && pc_p == 1 && c2_p <= 3.0 && c2_p == c2 + inc && !passed)
   || (pc == 0 && pc_p == 1 && c2_p == inc && passed && c2_p <= 3.0)
   || (pc == 1 && pc_p == 0 && c2_p == c2 + inc && c2 >= 3.0 && !passed)
}
 
function {:inline true} dc2init(pc : int, c3:real, inc: real, 
                                current: int, goal : int) returns (bool) 
   { pc == 0 && c3 == inc && current == goal }
function {:inline true} dc2trans
   (pc : int, pc_p: int, c3: real, c3_p:real, inc:real, 
   stop: bool, current_p: int, goal_p : int) 
   returns (bool)
{
   (pc == 0 && pc_p == 0 && c3_p == c3 + inc && current_p == goal_p)
   || (pc == 0 && pc_p == 1 && c3_p == c3 + inc && current_p != goal_p)
   || (pc == 1 && pc_p == 1 && c3_p == c3 + inc && current_p != goal_p)
   || (pc == 1 && pc_p == 2 && c3_p == inc      && current_p == goal_p && c3 < 2.0)
   || (pc == 2 && pc_p == 1 && c3_p == c3 + inc && current_p != goal_p)
   || (pc == 2 && pc_p == 2 && c3_p == c3 + inc && current_p == goal_p
          && c3 < 2.0 && !stop)
   || (pc == 2 && pc_p == 0 && c3_p == c3 + inc && current_p == goal_p && stop)
}

procedure elevator()
{
   var csppc, dc1pc, dc2pc : int;
   var current, goal, dir : int;
   var c2, c3, inc : real;

   var csppc_p, dc1pc_p, dc2pc_p : int;
   var current_p, goal_p, dir_p : int;
   var c2_p, c3_p : real;

   var start, stop, passed, newgoal : bool;

   assume (inc > 0.0);
   assume (cspinit(csppc)
           && zinit(goal, current, dir)
           && dc1init(dc1pc, c2, inc)
           && dc2init(dc2pc, c3, inc, current, goal));

   while (true) {
      havoc inc;
      havoc csppc_p, dc1pc_p, dc2pc_p;
      havoc current_p, goal_p, dir_p;
      havoc c2_p, c3_p;
      havoc start, stop, passed, newgoal;
      assume (inc > 0.0);

      assume (csptrans(csppc, csppc_p, newgoal, start, stop, passed)
           && ztrans(goal, goal_p, current, current_p, dir, dir_p,
                     newgoal, start, stop, passed)
           && dc1trans(dc1pc, dc1pc_p, c2, c2_p, inc, passed)
           && dc2trans(dc2pc, dc2pc_p, c3, c3_p, inc, stop, current_p,
           goal_p));

      csppc,dc1pc,dc2pc := csppc_p,dc1pc_p,dc2pc_p;
      current, goal, dir := current_p, goal_p, dir_p;
      c2, c3 := c2_p, c2_p;

      assert (Min <= current && current <= Max);
   }
      
}
 

