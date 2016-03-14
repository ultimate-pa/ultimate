//#Safe
type sync_state;
const unique sync_none : sync_state;
const unique waiting : sync_state;

type channel_id;
const unique chan_a : channel_id;
var channel : channel_id;

type automaton_id;
const unique A : automaton_id;
const unique B : automaton_id;
var sender : automaton_id;

type locationA;
const unique a0 : locationA;
const unique a1 : locationA;

type locationB;
const unique b0 : locationB;
const unique b1 : locationB;

var sync_channel : channel_id;
var sync : sync_state;

var delay : real;
var loc_A : locationA;
var loc_B : locationB;

var x : real;
var x_new : real; // variable to hold the resetted value of x 
var x_reset : bool; // true if there is a scheduled reset for x
var steps : int;
// if there were any edges that send a synchronization and update steps, there would be a steps_new variable
var A_power : real;

// sets the variables necessary to indicate that x will be reset at the next transition
procedure schedule_reset_x( value : real ) returns();
modifies x_new, x_reset;
ensures x_new == value;
ensures x_reset;

// perform all scheduled resets and clears the reset flags
procedure perform_resets() returns ();
modifies x, x_reset;
ensures old(x_reset) ==> (x == x_new && !x_reset);

function { :inline true } invariant_a0( x : real ) returns (bool) {
	x <= 5.0
}

function { :inline true } invariant_a1( x : real ) returns (bool) {
	x <= 6.0
}

function { :inline true } invariant_b0( x : real ) returns (bool) {
	true
}


function { :inline true } invariant_b1( x : real ) returns (bool) {
	x <= 5.0
}

function { :inline true } guard_phi_1( x: real ) returns (bool) {
	x >= 4.0
}

function { :inline true } guard_phi_3( x : real ) returns (bool) {
	x >= 5.0
}

function { :inline true } guard_phi_5( x : real ) returns (bool) {
	x <= 1.0
}

function { :inline true } property ( x : real, steps : int, A_power : real) returns (bool) {
	steps < 5 ==> A_power < 3000.0
}

procedure main() returns () 
modifies sync_channel, sync, delay, loc_A, loc_B, steps, A_power, sender, channel;
modifies x, x_new, x_reset;
{
// *** INITIALIZATION *** //
loc_A := a0;
loc_B := b0;
sync := sync_none; // can be none, waiting
A_power := 0.0;
x := 0.0;
steps := 0;

step: assert property(x, steps, A_power);
// Guess the right dela
havoc delay;
assume delay >= 0.0;

update_clocks:
// for all clocks c, do c := c + delay;
x := x + delay;
// update power vars
if (loc_A == a0) { A_power := A_power + delay * 0.5; }
if (loc_A == a1) { A_power := A_power + delay * 10.0; }

goto check_inv_A;
inv_A_checked:
goto check_inv_B;
inv_B_checked:
assert property(x, steps, A_power);
// non-deterministically choose an automaton to make a step
goto step_A, step_B;

//***** AUTOMATON A
step_A:
if (sync == sync_none) { // All steps that do not wait for a synchronization
	if (loc_A == a0) { // for locationAtion a0
		if (guard_phi_1(x)) {
			loc_A := a1; // move to the destination location
			// perform updates and resets
			steps := steps + 1;
			goto step; // step taken
		}
	}
	if (loc_A == a1) {
		if (true) {
			sender := A;
			sync := waiting;
			channel := chan_a;
			loc_A := a0;
			call schedule_reset_x(0.0);
			// non-deterministically let any of the other automata take a step
			goto step_B; // Here we would have a list of every other automaton that synchronizes on chanel 'a'
		}
	}
}

if (sync == waiting && sender != A) {
// no locations with receiving edges
}

goto deadlock;

//***** AUTOMATON B
step_B:
if (sync == sync_none) {
	if (loc_B == b1) {
		if (true) {
			loc_B := b0;
			// do updates
			goto step; // step taken
		}
		if (guard_phi_5(x)) {
			// self loop, do not update location
			// do updates
			steps := steps + 1;
			goto step; // step taken
		}
	}
}

if (sync == waiting && sender != B) {
	if (loc_B == b0 && channel == chan_a) {
		if (guard_phi_3(x)) { // receiver of synchronization
			sync := sync_none; // remove the sync flag
			loc_B := b1;
			call perform_resets();
			goto step; // step completed by synchronizing
		}
	}
}
goto deadlock;

///*** INVARIANT CHECKS ***///
check_inv_A:
if (loc_A == a0) { assume invariant_a0(x); goto inv_A_checked; }
if (loc_A == a1) { assume invariant_a1(x); goto inv_A_checked; }
goto deadlock;
check_inv_B:
if (loc_B == b0) { assume invariant_b0(x); goto inv_B_checked; }
if (loc_B == b1) { assume invariant_b1(x); goto inv_B_checked; }
goto deadlock;
deadlock:
}