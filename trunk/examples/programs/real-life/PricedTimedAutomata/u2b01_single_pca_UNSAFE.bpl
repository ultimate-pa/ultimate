//#Unsafe
type sync_state;
const unique sync_none: sync_state;
const unique waiting: sync_state;
const unique sync_broadcast: sync_state;
// Syncronization state
var sync: sync_state;

type AutomatonID;
const unique Template_1: AutomatonID;
var sender: AutomatonID;

type Template_1_Location;
// Location 'power100'
const unique id0_1: Template_1_Location;
// Location 'power5'
const unique id1_1: Template_1_Location;
var loc$Template_1: Template_1_Location;

var delay: real;

type channelID;
var sync_channel: channelID;

// Clock time (global)
var time: real;
var time$new: real;
var time$reset: bool;
procedure schedule_reset_time (value: real) returns ();
modifies time$new, time$reset;
ensures time$new == value;
ensures time$reset;

// Clock x (global)
var x: real;
var x$new: real;
var x$reset: bool;
procedure schedule_reset_x (value: real) returns ();
modifies x$new, x$reset;
ensures x$new == value;
ensures x$reset;

// Clock power (Template_1)
var Template_1$power: real;

// Procedure that performs all scheduled variable updates
procedure perform_resets () returns ();
modifies time, time$reset, x, x$reset;
ensures old(time$reset) ==> (time == time$new && !time$reset);
ensures !old(time$reset) ==> (time == old(time) && !time$reset);
ensures old(x$reset) ==> (x == x$new && !x$reset);
ensures !old(x$reset) ==> (x == old(x) && !x$reset);

// Location Invariants
function { :inline true } invariant_id0_1 (time: real, x: real) returns (bool)
{ x <= 11.0 }
function { :inline true } invariant_id1_1 (time: real, x: real) returns (bool)
{ x <= 10.0 }
// Transition guards
function { :inline true } guard_t1 (time: real, x: real) returns (bool)
{ x >= 10.0 }
function { :inline true } guard_t0 (time: real, x: real) returns (bool)
{ true }
function { :inline true } property (time: real, x: real, Template_1$power: real) returns (bool)
{ Template_1$power <= 3000.0 }

procedure main () returns ()
modifies sync, sync_channel, sender, delay, loc$Template_1, Template_1$power, time, time$new, time$reset, x, x$new, x$reset;
requires time == 0.0;
requires x == 0.0;
requires time$new == time;
requires x$new == x;
requires !time$reset;
requires !x$reset;
{
  // *** INITIALIZATION *** //
  sync := sync_none;
  loc$Template_1 := id1_1;
  Template_1$power := 0.0;
  
uppaal2boogie$step:
  assert property(time, x, Template_1$power);
  havoc delay;
  assume delay >= 0.0;
  // Update clocks
  time := time + delay;
  time$new := time;
  x := x + delay;
  x$new := x;
  // Update power variables
  if (loc$Template_1 == id0_1)
  {
    Template_1$power := Template_1$power + 100.0 * delay;
  }
  else  if (loc$Template_1 == id1_1)
  {
    Template_1$power := Template_1$power + 5.0 * delay;
  }
  // Invariant checks
  if (loc$Template_1 == id0_1)
  {
    assume invariant_id0_1(time, x);
    goto inv_checked_Template_1;
  }
  else  if (loc$Template_1 == id1_1)
  {
    assume invariant_id1_1(time, x);
    goto inv_checked_Template_1;
  }
  goto deadlock;
inv_checked_Template_1:
  
  assert property(time, x, Template_1$power);
  goto step_Template_1;
step_Template_1:
  if (sync == sync_none)
  {
    if (loc$Template_1 == id1_1)
    {
      goto transition$t1;
transition$t1:
      assume guard_t1(time,x);
      loc$Template_1 := id0_1;
      goto uppaal2boogie$step;
    }
    else    if (loc$Template_1 == id0_1)
    {
      goto transition$t0;
transition$t0:
      assume guard_t0(time,x);
      loc$Template_1 := id1_1;
      x := 0.0;
      x$new := x;
      goto uppaal2boogie$step;
    }
  }
  else  if (sync == waiting && sender != Template_1)
  {
  }
  goto deadlock;
  // *** Broadcast Receivers ***
deadlock:
}
