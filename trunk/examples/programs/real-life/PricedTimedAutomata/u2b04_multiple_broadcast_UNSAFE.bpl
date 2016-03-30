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
const unique id2_1: A1_1_Location;
var loc$A1_1: A1_1_Location;

type A2_1_Location;
const unique id3_1: A2_1_Location;
const unique id4_1: A2_1_Location;
const unique id5_1: A2_1_Location;
const unique id6_1: A2_1_Location;
var loc$A2_1: A2_1_Location;

type A3_1_Location;
const unique id7_1: A3_1_Location;
const unique id8_1: A3_1_Location;
const unique id9_1: A3_1_Location;
const unique id10_1: A3_1_Location;
var loc$A3_1: A3_1_Location;

var delay: real;

type channelID;
var sync_channel: channelID;

// Channel a (broadcast)
const unique chan_a: channelID;
// Channel c (broadcast)
const unique chan_c: channelID;
// Channel b
const unique chan_b: channelID;
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
function { :inline true } invariant_id8_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id2_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id3_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id7_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id4_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id6_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id9_1 (v: int) returns (bool)
{ true }
function { :inline true } invariant_id10_1 (v: int) returns (bool)
{ true }
// Transition guards
function { :inline true } guard_t1 (v: int) returns (bool)
{ true }
function { :inline true } guard_t7 (v: int) returns (bool)
{ true }
function { :inline true } guard_t3 (v: int) returns (bool)
{ true }
function { :inline true } guard_t5 (v: int) returns (bool)
{ true }
function { :inline true } guard_t4 (v: int) returns (bool)
{ true }
function { :inline true } guard_t8 (v: int) returns (bool)
{ true }
function { :inline true } guard_t0 (v: int) returns (bool)
{ true }
function { :inline true } guard_t6 (v: int) returns (bool)
{ true }
function { :inline true } guard_t2 (v: int) returns (bool)
{ true }
function { :inline true } property (v: int) returns (bool)
{ v != 1 }

procedure main () returns ()
modifies sync, sync_channel, sender, delay, loc$A1_1, loc$A2_1, loc$A3_1, v, v$new, v$reset;
requires v == 0;
requires v$new == v;
requires !v$reset;
{
  // *** INITIALIZATION *** //
  sync := sync_none;
  loc$A1_1 := id2_1;
  loc$A2_1 := id6_1;
  loc$A3_1 := id8_1;
  
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
  else  if (loc$A1_1 == id2_1)
  {
    assume invariant_id2_1(v);
    goto inv_checked_A1_1;
  }
  goto deadlock;
inv_checked_A1_1:
  if (loc$A2_1 == id3_1)
  {
    assume invariant_id3_1(v);
    goto inv_checked_A2_1;
  }
  else  if (loc$A2_1 == id4_1)
  {
    assume invariant_id4_1(v);
    goto inv_checked_A2_1;
  }
  else  if (loc$A2_1 == id5_1)
  {
    assume invariant_id5_1(v);
    goto inv_checked_A2_1;
  }
  else  if (loc$A2_1 == id6_1)
  {
    assume invariant_id6_1(v);
    goto inv_checked_A2_1;
  }
  goto deadlock;
inv_checked_A2_1:
  if (loc$A3_1 == id7_1)
  {
    assume invariant_id7_1(v);
    goto inv_checked_A3_1;
  }
  else  if (loc$A3_1 == id8_1)
  {
    assume invariant_id8_1(v);
    goto inv_checked_A3_1;
  }
  else  if (loc$A3_1 == id9_1)
  {
    assume invariant_id9_1(v);
    goto inv_checked_A3_1;
  }
  else  if (loc$A3_1 == id10_1)
  {
    assume invariant_id10_1(v);
    goto inv_checked_A3_1;
  }
  goto deadlock;
inv_checked_A3_1:
  
  assert property(v);
  goto step_A1_1, step_A2_1, step_A3_1;
step_A1_1:
  if (sync == sync_none)
  {
    if (loc$A1_1 == id2_1)
    {
      goto transition$t2;
transition$t2:
      assume guard_t2(v);
      loc$A1_1 := id1_1;
      call schedule_reset_v(1);
      sync := sync_broadcast;
      sync_channel := chan_a;
      sender := A1_1;
      goto broadcast_rcv$a;
    }
    else    if (loc$A1_1 == id1_1)
    {
      goto transition$t1;
transition$t1:
      assume guard_t1(v);
      loc$A1_1 := id0_1;
      sync := waiting;
      sync_channel := chan_b;
      sender := A1_1;
      goto step_A3_1, step_A2_1;
    }
    else    if (loc$A1_1 == id0_1)
    {
      goto transition$t0;
transition$t0:
      assume guard_t0(v);
      loc$A1_1 := id2_1;
      sync := sync_broadcast;
      sync_channel := chan_c;
      sender := A1_1;
      goto broadcast_rcv$c;
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
    if (loc$A2_1 == id5_1)
    {
      goto transition$t4;
transition$t4:
      assume guard_t4(v);
      assume sync_channel == chan_b;
      loc$A2_1 := id4_1;
      sync := sync_none;
      call perform_resets();
      goto uppaal2boogie$step;
    }
  }
  goto deadlock;
step_A3_1:
  if (sync == sync_none)
  {
  }
  else  if (sync == waiting && sender != A3_1)
  {
    if (loc$A3_1 == id7_1)
    {
      goto transition$t8;
transition$t8:
      assume guard_t8(v);
      assume sync_channel == chan_b;
      loc$A3_1 := id9_1;
      sync := sync_none;
      call perform_resets();
      goto uppaal2boogie$step;
    }
  }
  goto deadlock;
  // *** Broadcast Receivers ***
  // Begin channel a
broadcast_rcv$a:
  // Template A2_1
  if (sender != A2_1)
  {
    if (loc$A2_1 == id6_1)
    {
      goto transition$t5, broadcast_rcvr_done$A2_1$a$id6_1$negative;
transition$t5:
      assume guard_t5(v);
      loc$A2_1 := id5_1;
      call schedule_reset_v(2);
      goto broadcast_rcvr_done$a$A2_1;
broadcast_rcvr_done$A2_1$a$id6_1$negative:
      assume !guard_t5(v);
    }
  }
broadcast_rcvr_done$a$A2_1:
  // Template A3_1
  if (sender != A3_1)
  {
    if (loc$A3_1 == id8_1)
    {
      goto transition$t6, broadcast_rcvr_done$A3_1$a$id8_1$negative;
transition$t6:
      assume guard_t6(v);
      loc$A3_1 := id7_1;
      call schedule_reset_v(3);
      goto broadcast_rcvr_done$a$A3_1;
broadcast_rcvr_done$A3_1$a$id8_1$negative:
      assume !guard_t6(v);
    }
  }
broadcast_rcvr_done$a$A3_1:
  // All receivers processed for channel a
  call perform_resets();
  sync := sync_none;
  goto uppaal2boogie$step;
  // End channel a
  // Begin channel c
broadcast_rcv$c:
  // Template A2_1
  if (sender != A2_1)
  {
    if (loc$A2_1 == id4_1)
    {
      goto transition$t3, broadcast_rcvr_done$A2_1$c$id4_1$negative;
transition$t3:
      assume guard_t3(v);
      loc$A2_1 := id3_1;
      goto broadcast_rcvr_done$c$A2_1;
broadcast_rcvr_done$A2_1$c$id4_1$negative:
      assume !guard_t3(v);
    }
  }
broadcast_rcvr_done$c$A2_1:
  // Template A3_1
  if (sender != A3_1)
  {
    if (loc$A3_1 == id9_1)
    {
      goto transition$t7, broadcast_rcvr_done$A3_1$c$id9_1$negative;
transition$t7:
      assume guard_t7(v);
      loc$A3_1 := id10_1;
      goto broadcast_rcvr_done$c$A3_1;
broadcast_rcvr_done$A3_1$c$id9_1$negative:
      assume !guard_t7(v);
    }
  }
broadcast_rcvr_done$c$A3_1:
  // All receivers processed for channel c
  call perform_resets();
  sync := sync_none;
  goto uppaal2boogie$step;
  // End channel c
deadlock:
}
