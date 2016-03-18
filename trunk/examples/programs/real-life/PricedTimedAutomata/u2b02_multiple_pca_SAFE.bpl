//#Safe
type sync_state;
const unique sync_none: sync_state;
const unique waiting: sync_state;
const unique sync_broadcast: sync_state;
// Syncronization state
var sync: sync_state;

type AutomatonID;
const unique A_1: AutomatonID;
const unique B_1: AutomatonID;
var sender: AutomatonID;

type A_1_Location;
// Location 'a1'
const unique id0_1: A_1_Location;
// Location 'a0'
const unique id1_1: A_1_Location;
var loc$A_1: A_1_Location;

type B_1_Location;
// Location 'b1'
const unique id2_1: B_1_Location;
// Location 'b0'
const unique id3_1: B_1_Location;
var loc$B_1: B_1_Location;

var delay: real;

type channelID;
var sync_channel: channelID;

// Channel a
const unique chan_a: channelID;
// Clock x (global)
var x: real;
var x$new: real;
var x$reset: bool;
procedure schedule_reset_x (value: real) returns ();
modifies x$new, x$reset;
ensures x$new == value;
ensures x$reset;

// Variable steps (global)
var steps: int;
var steps$new: int;
var steps$reset: bool;
procedure schedule_reset_steps (value: int) returns ();
modifies steps$new, steps$reset;
ensures steps$new == value;
ensures steps$reset;

// Clock power (A_1)
var A_1$power: real;

// Procedure that performs all scheduled variable updates
procedure perform_resets () returns ();
modifies x, x$reset, steps, steps$reset;
ensures old(x$reset) ==> (x == x$new && !x$reset);
ensures !old(x$reset) ==> (x == old(x) && !x$reset);
ensures old(steps$reset) ==> (steps == steps$new && !steps$reset);
ensures !old(steps$reset) ==> (steps == old(steps) && !steps$reset);

// Location Invariants
function { :inline true } invariant_id0_1 (x: real, steps: int) returns (bool)
{ x <= 6.0 }
function { :inline true } invariant_id1_1 (x: real, steps: int) returns (bool)
{ x <= 5.0 }
function { :inline true } invariant_id2_1 (x: real, steps: int) returns (bool)
{ x <= 5.0 }
function { :inline true } invariant_id3_1 (x: real, steps: int) returns (bool)
{ true }
// Transition guards
function { :inline true } guard_t1 (x: real, steps: int) returns (bool)
{ x >= 4.0 }
function { :inline true } guard_t3 (x: real, steps: int) returns (bool)
{ x <= 1.0 }
function { :inline true } guard_t4 (x: real, steps: int) returns (bool)
{ x >= 5.0 }
function { :inline true } guard_t0 (x: real, steps: int) returns (bool)
{ true }
function { :inline true } guard_t2 (x: real, steps: int) returns (bool)
{ true }
function { :inline true } property (x: real, steps: int, A_1$power: real) returns (bool)
{ steps <= 6 ==> A_1$power < 150.0 }

procedure main () returns ()
modifies sync, sync_channel, sender, delay, loc$A_1, loc$B_1, A_1$power, x, x$new, x$reset, steps, steps$new, steps$reset;
requires steps == 0;
requires x == 0.0;
requires x$new == x;
requires steps$new == steps;
requires !x$reset;
requires !steps$reset;
{
  // *** INITIALIZATION *** //
  sync := sync_none;
  loc$A_1 := id1_1;
  loc$B_1 := id3_1;
  A_1$power := 0.0;
  
uppaal2boogie$step:
  assert property(x, steps, A_1$power);
  havoc delay;
  assume delay >= 0.0;
  // Update clocks
  x := x + delay;
  x$new := x;
  // Update power variables
  if (loc$A_1 == id0_1)
  {
    A_1$power := A_1$power + 10.0 * delay;
  }
  else  if (loc$A_1 == id1_1)
  {
    A_1$power := A_1$power + 0.5 * delay;
  }
  // Invariant checks
  if (loc$A_1 == id0_1)
  {
    assume invariant_id0_1(x, steps);
    goto inv_checked_A_1;
  }
  else  if (loc$A_1 == id1_1)
  {
    assume invariant_id1_1(x, steps);
    goto inv_checked_A_1;
  }
  goto deadlock;
inv_checked_A_1:
  if (loc$B_1 == id2_1)
  {
    assume invariant_id2_1(x, steps);
    goto inv_checked_B_1;
  }
  else  if (loc$B_1 == id3_1)
  {
    assume invariant_id3_1(x, steps);
    goto inv_checked_B_1;
  }
  goto deadlock;
inv_checked_B_1:
  
  assert property(x, steps, A_1$power);
  goto step_A_1, step_B_1;
step_A_1:
  if (sync == sync_none)
  {
    if (loc$A_1 == id1_1)
    {
      goto transition$t1;
transition$t1:
      assume guard_t1(x,steps);
      loc$A_1 := id0_1;
      steps := steps$new + 1;
      steps$new := steps;
      goto uppaal2boogie$step;
    }
    else    if (loc$A_1 == id0_1)
    {
      goto transition$t0;
transition$t0:
      assume guard_t0(x,steps);
      loc$A_1 := id1_1;
      call schedule_reset_x(0.0);
      sync := waiting;
      sync_channel := chan_a;
      sender := A_1;
      goto step_B_1;
    }
  }
  else  if (sync == waiting && sender != A_1)
  {
  }
  goto deadlock;
step_B_1:
  if (sync == sync_none)
  {
    if (loc$B_1 == id2_1)
    {
      goto transition$t2, transition$t3;
transition$t2:
      assume guard_t2(x,steps);
      loc$B_1 := id3_1;
      goto uppaal2boogie$step;
transition$t3:
      assume guard_t3(x,steps);
      loc$B_1 := id2_1;
      steps := steps$new + 1;
      steps$new := steps;
      goto uppaal2boogie$step;
    }
  }
  else  if (sync == waiting && sender != B_1)
  {
    if (loc$B_1 == id3_1)
    {
      goto transition$t4;
transition$t4:
      assume guard_t4(x,steps);
      assume sync_channel == chan_a;
      loc$B_1 := id2_1;
      sync := sync_none;
      call perform_resets();
      goto uppaal2boogie$step;
    }
  }
  goto deadlock;
  // *** Broadcast Receivers ***
deadlock:
}
