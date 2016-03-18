//#Unsafe
type sync_state;
const unique sync_none: sync_state;
const unique waiting: sync_state;
const unique sync_broadcast: sync_state;
// Syncronization state
var sync: sync_state;

type AutomatonID;
const unique A1_1: AutomatonID;
const unique A2_1: AutomatonID;
const unique A3_1: AutomatonID;
var sender: AutomatonID;

type A1_1_Location;
const unique id0_1: A1_1_Location;
const unique id1_1: A1_1_Location;
var loc$A1_1: A1_1_Location;

type A2_1_Location;
const unique id2_1: A2_1_Location;
const unique id3_1: A2_1_Location;
var loc$A2_1: A2_1_Location;

type A3_1_Location;
const unique id4_1: A3_1_Location;
const unique id5_1: A3_1_Location;
var loc$A3_1: A3_1_Location;

var delay: real;

type channelID;
var sync_channel: channelID;

// Channel a (broadcast)
const unique chan_a: channelID;
// Variable v (global)
var v: int;
var v$new: int;
var v$reset: bool;
procedure schedule_reset_v (value: int) returns ();
modifies v$new, v$reset;
ensures v$new == value;
ensures v$reset;

// Procedure that performs all scheduled variable updates
procedure perform_resets () returns ();
modifies v, v$reset;
ensures old(v$reset) ==> (v == v$new && !v$reset);
ensures !old(v$reset) ==> (v == old(v) && !v$reset);

// Location Invariants
function { :inline true } invariant_id0_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id1_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id5_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id2_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id3_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id4_1 (v: int) returns (bool)
{ true }
// Transition guards
function { :inline true } guard_t1 (v: int) returns (bool)
{ true }
function { :inline true } guard_t0 (v: int) returns (bool)
{ true }
function { :inline true } guard_t2 (v: int) returns (bool)
{ true }
function { :inline true } property (v: int) returns (bool)
{ v != 3 }

procedure main () returns ()
modifies sync, sync_channel, sender, delay, loc$A1_1, loc$A2_1, loc$A3_1, v, v$new, v$reset;
requires v == 0;
requires v$new == v;
requires !v$reset;
{
  // *** INITIALIZATION *** //
  sync := sync_none;
  loc$A1_1 := id1_1;
  loc$A2_1 := id3_1;
  loc$A3_1 := id5_1;
  
uppaal2boogie$step:
  assert property(v);
  havoc delay;
  assume delay >= 0.0;
  // Update clocks
  // Update power variables
  // Invariant checks
  if (loc$A1_1 == id0_1)
  {
    assume invariant_id0_1(v);
    goto inv_checked_A1_1;
  }
  else  if (loc$A1_1 == id1_1)
  {
    assume invariant_id1_1(v);
    goto inv_checked_A1_1;
  }
  goto deadlock;
inv_checked_A1_1:
  if (loc$A2_1 == id2_1)
  {
    assume invariant_id2_1(v);
    goto inv_checked_A2_1;
  }
  else  if (loc$A2_1 == id3_1)
  {
    assume invariant_id3_1(v);
    goto inv_checked_A2_1;
  }
  goto deadlock;
inv_checked_A2_1:
  if (loc$A3_1 == id4_1)
  {
    assume invariant_id4_1(v);
    goto inv_checked_A3_1;
  }
  else  if (loc$A3_1 == id5_1)
  {
    assume invariant_id5_1(v);
    goto inv_checked_A3_1;
  }
  goto deadlock;
inv_checked_A3_1:
  
  assert property(v);
  goto step_A1_1, step_A2_1, step_A3_1;
step_A1_1:
  if (sync == sync_none)
  {
    if (loc$A1_1 == id1_1)
    {
      goto transition$t0;
transition$t0:
      assume guard_t0(v);
      loc$A1_1 := id0_1;
      call schedule_reset_v(1);
      sync := sync_broadcast;
      sync_channel := chan_a;
      sender := A1_1;
      goto broadcast_rcv$a;
    }
  }
  else  if (sync == waiting && sender != A1_1)
  {
  }
  goto deadlock;
step_A2_1:
  if (sync == sync_none)
  {
  }
  else  if (sync == waiting && sender != A2_1)
  {
  }
  goto deadlock;
step_A3_1:
  if (sync == sync_none)
  {
  }
  else  if (sync == waiting && sender != A3_1)
  {
  }
  goto deadlock;
  // *** Broadcast Receivers ***
  // Begin channel a
broadcast_rcv$a:
  // Template A2_1
  if (sender != A2_1)
  {
    if (loc$A2_1 == id3_1)
    {
      goto transition$t1, broadcast_rcvr_done$A2_1$a$id3_1$negative;
transition$t1:
      assume guard_t1(v);
      loc$A2_1 := id2_1;
      call schedule_reset_v(2);
      goto broadcast_rcvr_done$a$A2_1;
broadcast_rcvr_done$A2_1$a$id3_1$negative:
      assume !guard_t1(v);
    }
  }
broadcast_rcvr_done$a$A2_1:
  // Template A3_1
  if (sender != A3_1)
  {
    if (loc$A3_1 == id5_1)
    {
      goto transition$t2, broadcast_rcvr_done$A3_1$a$id5_1$negative;
transition$t2:
      assume guard_t2(v);
      loc$A3_1 := id4_1;
      call schedule_reset_v(3);
      goto broadcast_rcvr_done$a$A3_1;
broadcast_rcvr_done$A3_1$a$id5_1$negative:
      assume !guard_t2(v);
    }
  }
broadcast_rcvr_done$a$A3_1:
  // All receivers processed for channel a
  call perform_resets();
  sync := sync_none;
  goto uppaal2boogie$step;
  // End channel a
deadlock:
}
