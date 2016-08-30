//#Unsafe
type sync_state;
const unique sync_none: sync_state;
const unique waiting: sync_state;
const unique sync_broadcast: sync_state;
// Syncronization state
var sync: sync_state;

type AutomatonID;
const unique MAC_1: AutomatonID;
const unique APP_RX_1: AutomatonID;
const unique APP_LZ_1: AutomatonID;
const unique MEDIUM_1: AutomatonID;
const unique ENV_1: AutomatonID;
var sender: AutomatonID;

type MAC_1_Location;
// Location 'RCV_ACK'
const unique id0_1: MAC_1_Location;
// Location 'SND_ACK'
const unique id1_1: MAC_1_Location;
const unique id2_1: MAC_1_Location;
// Location 'ACK_WAIT'
const unique id3_1: MAC_1_Location;
// Location 'SENDING'
const unique id4_1: MAC_1_Location;
// Location 'NOTIFIED'
const unique id5_1: MAC_1_Location;
// Location 'RECEIVED'
const unique id6_1: MAC_1_Location;
// Location 'SLOT_SLEEP'
const unique id7_1: MAC_1_Location;
// Location 'RECEIVING'
const unique id8_1: MAC_1_Location;
// Location 'SND_START'
const unique id9_1: MAC_1_Location;
// Location 'RCV_START'
const unique id10_1: MAC_1_Location;
// Location 'CHK_QUEUE'
const unique id11_1: MAC_1_Location;
// Location 'SLEEP'
const unique id12_1: MAC_1_Location;
var loc$MAC_1: MAC_1_Location;

type APP_RX_1_Location;
// Location 'PROCESS'
const unique id13_1: APP_RX_1_Location;
// Location 'IDLE'
const unique id14_1: APP_RX_1_Location;
var loc$APP_RX_1: APP_RX_1_Location;

type APP_LZ_1_Location;
// Location 'SENT'
const unique id15_1: APP_LZ_1_Location;
// Location 'IDLE'
const unique id16_1: APP_LZ_1_Location;
var loc$APP_LZ_1: APP_LZ_1_Location;

type MEDIUM_1_Location;
const unique id17_1: MEDIUM_1_Location;
const unique id18_1: MEDIUM_1_Location;
const unique id19_1: MEDIUM_1_Location;
const unique id20_1: MEDIUM_1_Location;
// Location 'START'
const unique id21_1: MEDIUM_1_Location;
// Location 'IDLE'
const unique id22_1: MEDIUM_1_Location;
var loc$MEDIUM_1: MEDIUM_1_Location;

type ENV_1_Location;
// Location 'SENT'
const unique id23_1: ENV_1_Location;
const unique id24_1: ENV_1_Location;
const unique id25_1: ENV_1_Location;
// Location 'SND_ACK'
const unique id26_1: ENV_1_Location;
// Location 'PROCESS'
const unique id27_1: ENV_1_Location;
// Location 'SND'
const unique id28_1: ENV_1_Location;
// Location 'RCV'
const unique id29_1: ENV_1_Location;
// Location 'LBT'
const unique id30_1: ENV_1_Location;
// Location 'SLEEP'
const unique id31_1: ENV_1_Location;
var loc$ENV_1: ENV_1_Location;

var delay: real;

type channelID;
var sync_channel: channelID;

// Variable Tic (global)
var Tic: int;
// Constant Tic skipped
// Variable Second (global)
var Second: int;
// Constant Second skipped
// Variable LBTInterval (global)
var LBTInterval: int;
// Constant LBTInterval skipped
// Variable MessageLength (global)
var MessageLength: int;
// Constant MessageLength skipped
// Variable Slot (global)
var Slot: int;
// Constant Slot skipped
// Variable Cycle (global)
var Cycle: int;
// Constant Cycle skipped
// Variable SleepTime (global)
var SleepTime: int;
// Constant SleepTime skipped
// Variable PacketProcessing (global)
var PacketProcessing: int;
// Constant PacketProcessing skipped
// Variable queue (global)
var queue: bool;
var queue$new: bool;
var queue$reset: bool;
procedure schedule_reset_queue (value: bool) returns ();
modifies queue$new, queue$reset;
ensures queue$new == value;
ensures queue$reset;

// Variable channelBusy (global)
var channelBusy: bool;
var channelBusy$new: bool;
var channelBusy$reset: bool;
procedure schedule_reset_channelBusy (value: bool) returns ();
modifies channelBusy$new, channelBusy$reset;
ensures channelBusy$new == value;
ensures channelBusy$reset;

// Channel RX_START (broadcast)
const unique chan_RX_START: channelID;
// Channel RX_END (broadcast)
const unique chan_RX_END: channelID;
// Channel COLLISION (broadcast)
const unique chan_COLLISION: channelID;
// Channel TX_START
const unique chan_TX_START: channelID;
// Channel TX_END
const unique chan_TX_END: channelID;
// Channel PKT_RCV
const unique chan_PKT_RCV: channelID;
// Channel ACK
const unique chan_ACK: channelID;
// Channel NO_ACK
const unique chan_NO_ACK: channelID;
// Clock time (global)
var time: real;
var time$new: real;
var time$reset: bool;
procedure schedule_reset_time (value: real) returns ();
modifies time$new, time$reset;
ensures time$new == value;
ensures time$reset;

// Clock t (MAC_1)
var MAC_1$t: real;
var MAC_1$t$new: real;
var MAC_1$t$reset: bool;
procedure schedule_reset_MAC_1$t (value: real) returns ();
modifies MAC_1$t$new, MAC_1$t$reset;
ensures MAC_1$t$new == value;
ensures MAC_1$t$reset;

// Clock t0 (MAC_1)
var MAC_1$t0: real;
var MAC_1$t0$new: real;
var MAC_1$t0$reset: bool;
procedure schedule_reset_MAC_1$t0 (value: real) returns ();
modifies MAC_1$t0$new, MAC_1$t0$reset;
ensures MAC_1$t0$new == value;
ensures MAC_1$t0$reset;

// Clock power (MAC_1)
var MAC_1$power: real;

// Clock t0 (APP_RX_1)
var APP_RX_1$t0: real;
var APP_RX_1$t0$new: real;
var APP_RX_1$t0$reset: bool;
procedure schedule_reset_APP_RX_1$t0 (value: real) returns ();
modifies APP_RX_1$t0$new, APP_RX_1$t0$reset;
ensures APP_RX_1$t0$new == value;
ensures APP_RX_1$t0$reset;

// Clock t0 (APP_LZ_1)
var APP_LZ_1$t0: real;
var APP_LZ_1$t0$new: real;
var APP_LZ_1$t0$reset: bool;
procedure schedule_reset_APP_LZ_1$t0 (value: real) returns ();
modifies APP_LZ_1$t0$new, APP_LZ_1$t0$reset;
ensures APP_LZ_1$t0$new == value;
ensures APP_LZ_1$t0$reset;

// Clock t0 (MEDIUM_1)
var MEDIUM_1$t0: real;
var MEDIUM_1$t0$new: real;
var MEDIUM_1$t0$reset: bool;
procedure schedule_reset_MEDIUM_1$t0 (value: real) returns ();
modifies MEDIUM_1$t0$new, MEDIUM_1$t0$reset;
ensures MEDIUM_1$t0$new == value;
ensures MEDIUM_1$t0$reset;

// Variable sendCount (MEDIUM_1)
var MEDIUM_1$sendCount: int;
var MEDIUM_1$sendCount$new: int;
var MEDIUM_1$sendCount$reset: bool;
procedure schedule_reset_MEDIUM_1$sendCount (value: int) returns ();
modifies MEDIUM_1$sendCount$new, MEDIUM_1$sendCount$reset;
ensures MEDIUM_1$sendCount$new == value;
ensures MEDIUM_1$sendCount$reset;

// Clock t (ENV_1)
var ENV_1$t: real;
var ENV_1$t$new: real;
var ENV_1$t$reset: bool;
procedure schedule_reset_ENV_1$t (value: real) returns ();
modifies ENV_1$t$new, ENV_1$t$reset;
ensures ENV_1$t$new == value;
ensures ENV_1$t$reset;

// Clock t0 (ENV_1)
var ENV_1$t0: real;
var ENV_1$t0$new: real;
var ENV_1$t0$reset: bool;
procedure schedule_reset_ENV_1$t0 (value: real) returns ();
modifies ENV_1$t0$new, ENV_1$t0$reset;
ensures ENV_1$t0$new == value;
ensures ENV_1$t0$reset;

// Procedure that performs all scheduled variable updates
procedure perform_resets () returns ();
modifies time, time$reset, ENV_1$t, ENV_1$t$reset, MAC_1$t0, MAC_1$t0$reset, APP_LZ_1$t0, APP_LZ_1$t0$reset, ENV_1$t0, ENV_1$t0$reset, MAC_1$t, MAC_1$t$reset, MEDIUM_1$t0, MEDIUM_1$t0$reset, APP_RX_1$t0, APP_RX_1$t0$reset, MEDIUM_1$sendCount, MEDIUM_1$sendCount$reset, channelBusy, channelBusy$reset, queue, queue$reset;
ensures old(time$reset) ==> (time == time$new && !time$reset);
ensures !old(time$reset) ==> (time == old(time) && !time$reset);
ensures old(ENV_1$t$reset) ==> (ENV_1$t == ENV_1$t$new && !ENV_1$t$reset);
ensures !old(ENV_1$t$reset) ==> (ENV_1$t == old(ENV_1$t) && !ENV_1$t$reset);
ensures old(MAC_1$t0$reset) ==> (MAC_1$t0 == MAC_1$t0$new && !MAC_1$t0$reset);
ensures !old(MAC_1$t0$reset) ==> (MAC_1$t0 == old(MAC_1$t0) && !MAC_1$t0$reset);
ensures old(APP_LZ_1$t0$reset) ==> (APP_LZ_1$t0 == APP_LZ_1$t0$new && !APP_LZ_1$t0$reset);
ensures !old(APP_LZ_1$t0$reset) ==> (APP_LZ_1$t0 == old(APP_LZ_1$t0) && !APP_LZ_1$t0$reset);
ensures old(ENV_1$t0$reset) ==> (ENV_1$t0 == ENV_1$t0$new && !ENV_1$t0$reset);
ensures !old(ENV_1$t0$reset) ==> (ENV_1$t0 == old(ENV_1$t0) && !ENV_1$t0$reset);
ensures old(MAC_1$t$reset) ==> (MAC_1$t == MAC_1$t$new && !MAC_1$t$reset);
ensures !old(MAC_1$t$reset) ==> (MAC_1$t == old(MAC_1$t) && !MAC_1$t$reset);
ensures old(MEDIUM_1$t0$reset) ==> (MEDIUM_1$t0 == MEDIUM_1$t0$new && !MEDIUM_1$t0$reset);
ensures !old(MEDIUM_1$t0$reset) ==> (MEDIUM_1$t0 == old(MEDIUM_1$t0) && !MEDIUM_1$t0$reset);
ensures old(APP_RX_1$t0$reset) ==> (APP_RX_1$t0 == APP_RX_1$t0$new && !APP_RX_1$t0$reset);
ensures !old(APP_RX_1$t0$reset) ==> (APP_RX_1$t0 == old(APP_RX_1$t0) && !APP_RX_1$t0$reset);
ensures old(MEDIUM_1$sendCount$reset) ==> (MEDIUM_1$sendCount == MEDIUM_1$sendCount$new && !MEDIUM_1$sendCount$reset);
ensures !old(MEDIUM_1$sendCount$reset) ==> (MEDIUM_1$sendCount == old(MEDIUM_1$sendCount) && !MEDIUM_1$sendCount$reset);
ensures old(channelBusy$reset) ==> (channelBusy == channelBusy$new && !channelBusy$reset);
ensures !old(channelBusy$reset) ==> (channelBusy == old(channelBusy) && !channelBusy$reset);
ensures old(queue$reset) ==> (queue == queue$new && !queue$reset);
ensures !old(queue$reset) ==> (queue == old(queue) && !queue$reset);

// Location Invariants
function { :inline true } invariant_id26_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 <= 8.0 }
function { :inline true } invariant_id13_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_RX_1$t0 <= 0.0 }
function { :inline true } invariant_id19_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id20_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id14_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id0_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id22_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id25_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t <= 20.0 }
function { :inline true } invariant_id1_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 8.0 }
function { :inline true } invariant_id17_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MEDIUM_1$t0 <= 0.0 }
function { :inline true } invariant_id5_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id15_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_LZ_1$t0 <= 9600.0 }
function { :inline true } invariant_id18_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MEDIUM_1$t0 <= 0.0 }
function { :inline true } invariant_id24_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t <= 20.0 }
function { :inline true } invariant_id8_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id16_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_LZ_1$t0 <= 0.0 }
function { :inline true } invariant_id29_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } invariant_id2_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 0.0 }
function { :inline true } invariant_id3_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t <= 20.0 }
function { :inline true } invariant_id23_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 <= 0.0 }
function { :inline true } invariant_id28_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 <= 8.0 }
function { :inline true } invariant_id7_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t <= 20.0 }
function { :inline true } invariant_id12_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t <= 380.0 }
function { :inline true } invariant_id27_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 <= 0.0 }
function { :inline true } invariant_id4_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 8.0 }
function { :inline true } invariant_id11_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 0.0 }
function { :inline true } invariant_id6_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 0.0 }
function { :inline true } invariant_id9_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 4.0 }
function { :inline true } invariant_id10_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 <= 12.0 }
function { :inline true } invariant_id21_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MEDIUM_1$t0 <= 0.0 }
function { :inline true } invariant_id30_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 <= 4.0 }
function { :inline true } invariant_id31_1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t <= 380.0 }
// Transition guards
function { :inline true } guard_t7 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t13 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t16 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t26 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t27 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MEDIUM_1$sendCount == 1 }
function { :inline true } guard_t43 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t20 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_RX_1$t0 >= 0.0 }
function { :inline true } guard_t23 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_LZ_1$t0 >= 9600.0 }
function { :inline true } guard_t32 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t8 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 >= 8.0 }
function { :inline true } guard_t9 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 > 0.0 && !channelBusy }
function { :inline true } guard_t38 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t28 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t2 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t33 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t29 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MEDIUM_1$sendCount == 1 }
function { :inline true } guard_t36 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t >= 20.0 }
function { :inline true } guard_t10 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t18 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ !queue }
function { :inline true } guard_t30 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MEDIUM_1$sendCount > 1 }
function { :inline true } guard_t24 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_LZ_1$t0 >= 0.0 && APP_LZ_1$t0 <= 9600.0 }
function { :inline true } guard_t1 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 >= 8.0 }
function { :inline true } guard_t19 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t >= 380.0 }
function { :inline true } guard_t34 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t42 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t11 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t14 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t >= 20.0 }
function { :inline true } guard_t25 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t37 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t3 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 >= 4.0 }
function { :inline true } guard_t5 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t >= 20.0 }
function { :inline true } guard_t31 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t21 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ APP_RX_1$t0 >= 0.0 }
function { :inline true } guard_t4 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t39 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t >= 20.0 }
function { :inline true } guard_t45 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t >= 380.0 }
function { :inline true } guard_t17 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ queue }
function { :inline true } guard_t40 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t0 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t12 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t15 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ MAC_1$t0 >= 12.0 }
function { :inline true } guard_t6 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t35 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 >= 8.0 }
function { :inline true } guard_t44 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t22 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ true }
function { :inline true } guard_t41 (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool) returns (bool)
{ ENV_1$t0 >= 0.0 }
function { :inline true } property (time: real, ENV_1$t: real, MAC_1$t0: real, APP_LZ_1$t0: real, ENV_1$t0: real, MAC_1$t: real, MEDIUM_1$t0: real, APP_RX_1$t0: real, MEDIUM_1$sendCount: int, channelBusy: bool, queue: bool, MAC_1$power: real) returns (bool)
{ time <= 400.0 ==> MAC_1$power < 100.0 }

procedure main () returns ()
modifies sync, sync_channel, sender, delay, loc$MAC_1, loc$APP_RX_1, loc$APP_LZ_1, loc$MEDIUM_1, loc$ENV_1, MAC_1$power, time, time$new, time$reset, ENV_1$t, ENV_1$t$new, ENV_1$t$reset, MAC_1$t0, MAC_1$t0$new, MAC_1$t0$reset, APP_LZ_1$t0, APP_LZ_1$t0$new, APP_LZ_1$t0$reset, ENV_1$t0, ENV_1$t0$new, ENV_1$t0$reset, MAC_1$t, MAC_1$t$new, MAC_1$t$reset, MEDIUM_1$t0, MEDIUM_1$t0$new, MEDIUM_1$t0$reset, APP_RX_1$t0, APP_RX_1$t0$new, APP_RX_1$t0$reset, MEDIUM_1$sendCount, MEDIUM_1$sendCount$new, MEDIUM_1$sendCount$reset, channelBusy, channelBusy$new, channelBusy$reset, queue, queue$new, queue$reset;
requires MEDIUM_1$sendCount == 0;
requires time == 0.0;
requires ENV_1$t == 0.0;
requires MAC_1$t0 == 0.0;
requires APP_LZ_1$t0 == 0.0;
requires ENV_1$t0 == 0.0;
requires MAC_1$t == 0.0;
requires MEDIUM_1$t0 == 0.0;
requires APP_RX_1$t0 == 0.0;
requires channelBusy == false;
requires queue == false;
requires time$new == time;
requires ENV_1$t$new == ENV_1$t;
requires MAC_1$t0$new == MAC_1$t0;
requires APP_LZ_1$t0$new == APP_LZ_1$t0;
requires ENV_1$t0$new == ENV_1$t0;
requires MAC_1$t$new == MAC_1$t;
requires MEDIUM_1$t0$new == MEDIUM_1$t0;
requires APP_RX_1$t0$new == APP_RX_1$t0;
requires MEDIUM_1$sendCount$new == MEDIUM_1$sendCount;
requires channelBusy$new == channelBusy;
requires queue$new == queue;
requires !time$reset;
requires !ENV_1$t$reset;
requires !MAC_1$t0$reset;
requires !APP_LZ_1$t0$reset;
requires !ENV_1$t0$reset;
requires !MAC_1$t$reset;
requires !MEDIUM_1$t0$reset;
requires !APP_RX_1$t0$reset;
requires !MEDIUM_1$sendCount$reset;
requires !channelBusy$reset;
requires !queue$reset;
{
  // *** INITIALIZATION *** //
  sync := sync_none;
  loc$MAC_1 := id12_1;
  loc$APP_RX_1 := id14_1;
  loc$APP_LZ_1 := id16_1;
  loc$MEDIUM_1 := id22_1;
  loc$ENV_1 := id31_1;
  MAC_1$power := 0.0;
  
uppaal2boogie$step:
  assert property(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue, MAC_1$power);
  havoc delay;
  assume delay >= 0.0;
  // Update clocks
  time := time + delay;
  time$new := time;
  ENV_1$t := ENV_1$t + delay;
  ENV_1$t$new := ENV_1$t;
  MAC_1$t0 := MAC_1$t0 + delay;
  MAC_1$t0$new := MAC_1$t0;
  APP_LZ_1$t0 := APP_LZ_1$t0 + delay;
  APP_LZ_1$t0$new := APP_LZ_1$t0;
  ENV_1$t0 := ENV_1$t0 + delay;
  ENV_1$t0$new := ENV_1$t0;
  MAC_1$t := MAC_1$t + delay;
  MAC_1$t$new := MAC_1$t;
  MEDIUM_1$t0 := MEDIUM_1$t0 + delay;
  MEDIUM_1$t0$new := MEDIUM_1$t0;
  APP_RX_1$t0 := APP_RX_1$t0 + delay;
  APP_RX_1$t0$new := APP_RX_1$t0;
  // Update power variables
  if (loc$MAC_1 == id0_1)
  {
    MAC_1$power := MAC_1$power + 30.0 * delay;
  }
  else  if (loc$MAC_1 == id1_1)
  {
    MAC_1$power := MAC_1$power + 50.0 * delay;
  }
  else  if (loc$MAC_1 == id2_1)
  {
    MAC_1$power := MAC_1$power + 50.0 * delay;
  }
  else  if (loc$MAC_1 == id3_1)
  {
    MAC_1$power := MAC_1$power + 30.0 * delay;
  }
  else  if (loc$MAC_1 == id4_1)
  {
    MAC_1$power := MAC_1$power + 50.0 * delay;
  }
  else  if (loc$MAC_1 == id5_1)
  {
    MAC_1$power := MAC_1$power + 0.005 * delay;
  }
  else  if (loc$MAC_1 == id7_1)
  {
    MAC_1$power := MAC_1$power + 0.005 * delay;
  }
  else  if (loc$MAC_1 == id8_1)
  {
    MAC_1$power := MAC_1$power + 30.0 * delay;
  }
  else  if (loc$MAC_1 == id9_1)
  {
    MAC_1$power := MAC_1$power + 30.0 * delay;
  }
  else  if (loc$MAC_1 == id10_1)
  {
    MAC_1$power := MAC_1$power + 30.0 * delay;
  }
  else  if (loc$MAC_1 == id12_1)
  {
    MAC_1$power := MAC_1$power + 0.005 * delay;
  }
  // Invariant checks
  if (loc$MAC_1 == id0_1)
  {
    assume invariant_id0_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id1_1)
  {
    assume invariant_id1_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id2_1)
  {
    assume invariant_id2_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id3_1)
  {
    assume invariant_id3_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id4_1)
  {
    assume invariant_id4_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id5_1)
  {
    assume invariant_id5_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id6_1)
  {
    assume invariant_id6_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id7_1)
  {
    assume invariant_id7_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id8_1)
  {
    assume invariant_id8_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id9_1)
  {
    assume invariant_id9_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id10_1)
  {
    assume invariant_id10_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id11_1)
  {
    assume invariant_id11_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  else  if (loc$MAC_1 == id12_1)
  {
    assume invariant_id12_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MAC_1;
  }
  goto deadlock;
inv_checked_MAC_1:
  if (loc$APP_RX_1 == id13_1)
  {
    assume invariant_id13_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_APP_RX_1;
  }
  else  if (loc$APP_RX_1 == id14_1)
  {
    assume invariant_id14_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_APP_RX_1;
  }
  goto deadlock;
inv_checked_APP_RX_1:
  if (loc$APP_LZ_1 == id15_1)
  {
    assume invariant_id15_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_APP_LZ_1;
  }
  else  if (loc$APP_LZ_1 == id16_1)
  {
    assume invariant_id16_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_APP_LZ_1;
  }
  goto deadlock;
inv_checked_APP_LZ_1:
  if (loc$MEDIUM_1 == id17_1)
  {
    assume invariant_id17_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MEDIUM_1;
  }
  else  if (loc$MEDIUM_1 == id18_1)
  {
    assume invariant_id18_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MEDIUM_1;
  }
  else  if (loc$MEDIUM_1 == id19_1)
  {
    assume invariant_id19_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MEDIUM_1;
  }
  else  if (loc$MEDIUM_1 == id20_1)
  {
    assume invariant_id20_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MEDIUM_1;
  }
  else  if (loc$MEDIUM_1 == id21_1)
  {
    assume invariant_id21_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MEDIUM_1;
  }
  else  if (loc$MEDIUM_1 == id22_1)
  {
    assume invariant_id22_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_MEDIUM_1;
  }
  goto deadlock;
inv_checked_MEDIUM_1:
  if (loc$ENV_1 == id23_1)
  {
    assume invariant_id23_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id24_1)
  {
    assume invariant_id24_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id25_1)
  {
    assume invariant_id25_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id26_1)
  {
    assume invariant_id26_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id27_1)
  {
    assume invariant_id27_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id28_1)
  {
    assume invariant_id28_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id29_1)
  {
    assume invariant_id29_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id30_1)
  {
    assume invariant_id30_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  else  if (loc$ENV_1 == id31_1)
  {
    assume invariant_id31_1(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue);
    goto inv_checked_ENV_1;
  }
  goto deadlock;
inv_checked_ENV_1:
  
  assert property(time, ENV_1$t, MAC_1$t0, APP_LZ_1$t0, ENV_1$t0, MAC_1$t, MEDIUM_1$t0, APP_RX_1$t0, MEDIUM_1$sendCount, channelBusy, queue, MAC_1$power);
  goto step_MAC_1, step_APP_RX_1, step_APP_LZ_1, step_MEDIUM_1, step_ENV_1;
step_MAC_1:
  if (sync == sync_none)
  {
    if (loc$MAC_1 == id12_1)
    {
      goto transition$t19;
transition$t19:
      assume guard_t19(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id11_1;
      MAC_1$t := 0.0;
      MAC_1$t$new := MAC_1$t;
      MAC_1$t0 := 0.0;
      MAC_1$t0$new := MAC_1$t0;
      goto uppaal2boogie$step;
    }
    else    if (loc$MAC_1 == id11_1)
    {
      goto transition$t17, transition$t18;
transition$t17:
      assume guard_t17(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id9_1;
      goto uppaal2boogie$step;
transition$t18:
      assume guard_t18(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id10_1;
      goto uppaal2boogie$step;
    }
    else    if (loc$MAC_1 == id10_1)
    {
      goto transition$t15;
transition$t15:
      assume guard_t15(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id7_1;
      goto uppaal2boogie$step;
    }
    else    if (loc$MAC_1 == id7_1)
    {
      goto transition$t14;
transition$t14:
      assume guard_t14(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id12_1;
      MAC_1$t := 0.0;
      MAC_1$t$new := MAC_1$t;
      goto uppaal2boogie$step;
    }
    else    if (loc$MAC_1 == id6_1)
    {
      goto transition$t11;
transition$t11:
      assume guard_t11(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id5_1;
      sync := waiting;
      sync_channel := chan_PKT_RCV;
      sender := MAC_1;
      goto step_APP_RX_1;
    }
    else    if (loc$MAC_1 == id4_1)
    {
      goto transition$t8;
transition$t8:
      assume guard_t8(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id3_1;
      call schedule_reset_queue(false);
      sync := waiting;
      sync_channel := chan_TX_END;
      sender := MAC_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$MAC_1 == id3_1)
    {
      goto transition$t5;
transition$t5:
      assume guard_t5(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id12_1;
      MAC_1$t := 0.0;
      MAC_1$t$new := MAC_1$t;
      goto uppaal2boogie$step;
    }
    else    if (loc$MAC_1 == id9_1)
    {
      goto transition$t3, transition$t9;
transition$t3:
      assume guard_t3(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id7_1;
      goto uppaal2boogie$step;
transition$t9:
      assume guard_t9(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id4_1;
      call schedule_reset_MAC_1$t0(0.0);
      sync := waiting;
      sync_channel := chan_TX_START;
      sender := MAC_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$MAC_1 == id2_1)
    {
      goto transition$t2;
transition$t2:
      assume guard_t2(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id1_1;
      sync := waiting;
      sync_channel := chan_TX_START;
      sender := MAC_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$MAC_1 == id1_1)
    {
      goto transition$t1;
transition$t1:
      assume guard_t1(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id7_1;
      sync := waiting;
      sync_channel := chan_TX_END;
      sender := MAC_1;
      goto step_MEDIUM_1;
    }
  }
  else  if (sync == waiting && sender != MAC_1)
  {
    if (loc$MAC_1 == id5_1)
    {
      goto transition$t7, transition$t12;
transition$t7:
      assume guard_t7(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_ACK;
      loc$MAC_1 := id2_1;
      sync := sync_none;
      call perform_resets();
      MAC_1$t0 := 0.0;
      MAC_1$t0$new := MAC_1$t0;
      goto uppaal2boogie$step;
transition$t12:
      assume guard_t12(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_NO_ACK;
      loc$MAC_1 := id7_1;
      sync := sync_none;
      call perform_resets();
      goto uppaal2boogie$step;
    }
  }
  goto deadlock;
step_APP_RX_1:
  if (sync == sync_none)
  {
    if (loc$APP_RX_1 == id13_1)
    {
      goto transition$t20, transition$t21;
transition$t20:
      assume guard_t20(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$APP_RX_1 := id14_1;
      sync := waiting;
      sync_channel := chan_NO_ACK;
      sender := APP_RX_1;
      goto step_MAC_1;
transition$t21:
      assume guard_t21(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$APP_RX_1 := id14_1;
      sync := waiting;
      sync_channel := chan_ACK;
      sender := APP_RX_1;
      goto step_MAC_1;
    }
  }
  else  if (sync == waiting && sender != APP_RX_1)
  {
    if (loc$APP_RX_1 == id14_1)
    {
      goto transition$t22;
transition$t22:
      assume guard_t22(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_PKT_RCV;
      loc$APP_RX_1 := id13_1;
      sync := sync_none;
      call perform_resets();
      APP_RX_1$t0 := 0.0;
      APP_RX_1$t0$new := APP_RX_1$t0;
      goto uppaal2boogie$step;
    }
  }
  goto deadlock;
step_APP_LZ_1:
  if (sync == sync_none)
  {
    if (loc$APP_LZ_1 == id16_1)
    {
      goto transition$t24;
transition$t24:
      assume guard_t24(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$APP_LZ_1 := id15_1;
      queue := true;
      queue$new := queue;
      goto uppaal2boogie$step;
    }
    else    if (loc$APP_LZ_1 == id15_1)
    {
      goto transition$t23;
transition$t23:
      assume guard_t23(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$APP_LZ_1 := id16_1;
      APP_LZ_1$t0 := 0.0;
      APP_LZ_1$t0$new := APP_LZ_1$t0;
      goto uppaal2boogie$step;
    }
  }
  else  if (sync == waiting && sender != APP_LZ_1)
  {
  }
  goto deadlock;
step_MEDIUM_1:
  if (sync == sync_none)
  {
    if (loc$MEDIUM_1 == id21_1)
    {
      goto transition$t32;
transition$t32:
      assume guard_t32(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MEDIUM_1 := id20_1;
      sync := sync_broadcast;
      sync_channel := chan_RX_START;
      sender := MEDIUM_1;
      goto broadcast_rcv$RX_START;
    }
    else    if (loc$MEDIUM_1 == id18_1)
    {
      goto transition$t28;
transition$t28:
      assume guard_t28(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MEDIUM_1 := id22_1;
      call schedule_reset_MEDIUM_1$sendCount(0);
      call schedule_reset_channelBusy(false);
      sync := sync_broadcast;
      sync_channel := chan_COLLISION;
      sender := MEDIUM_1;
      goto broadcast_rcv$COLLISION;
    }
    else    if (loc$MEDIUM_1 == id17_1)
    {
      goto transition$t26;
transition$t26:
      assume guard_t26(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MEDIUM_1 := id22_1;
      call schedule_reset_MEDIUM_1$sendCount(0);
      call schedule_reset_channelBusy(false);
      sync := sync_broadcast;
      sync_channel := chan_RX_END;
      sender := MEDIUM_1;
      goto broadcast_rcv$RX_END;
    }
  }
  else  if (sync == waiting && sender != MEDIUM_1)
  {
    if (loc$MEDIUM_1 == id22_1)
    {
      goto transition$t33;
transition$t33:
      assume guard_t33(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_TX_START;
      loc$MEDIUM_1 := id21_1;
      sync := sync_none;
      call perform_resets();
      MEDIUM_1$t0 := 0.0;
      MEDIUM_1$t0$new := MEDIUM_1$t0;
      MEDIUM_1$sendCount := 1;
      MEDIUM_1$sendCount$new := MEDIUM_1$sendCount;
      channelBusy := true;
      channelBusy$new := channelBusy;
      goto uppaal2boogie$step;
    }
    else    if (loc$MEDIUM_1 == id20_1)
    {
      goto transition$t27, transition$t31;
transition$t27:
      assume guard_t27(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_TX_END;
      loc$MEDIUM_1 := id17_1;
      sync := sync_none;
      call perform_resets();
      MEDIUM_1$t0 := 0.0;
      MEDIUM_1$t0$new := MEDIUM_1$t0;
      goto uppaal2boogie$step;
transition$t31:
      assume guard_t31(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_TX_START;
      loc$MEDIUM_1 := id19_1;
      sync := sync_none;
      call perform_resets();
      MEDIUM_1$sendCount := MEDIUM_1$sendCount$new + 1;
      MEDIUM_1$sendCount$new := MEDIUM_1$sendCount;
      goto uppaal2boogie$step;
    }
    else    if (loc$MEDIUM_1 == id19_1)
    {
      goto transition$t25, transition$t29, transition$t30;
transition$t25:
      assume guard_t25(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_TX_START;
      loc$MEDIUM_1 := id19_1;
      sync := sync_none;
      call perform_resets();
      MEDIUM_1$sendCount := MEDIUM_1$sendCount$new + 1;
      MEDIUM_1$sendCount$new := MEDIUM_1$sendCount;
      goto uppaal2boogie$step;
transition$t29:
      assume guard_t29(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_TX_END;
      loc$MEDIUM_1 := id18_1;
      sync := sync_none;
      call perform_resets();
      MEDIUM_1$t0 := 0.0;
      MEDIUM_1$t0$new := MEDIUM_1$t0;
      goto uppaal2boogie$step;
transition$t30:
      assume guard_t30(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      assume sync_channel == chan_TX_END;
      loc$MEDIUM_1 := id19_1;
      sync := sync_none;
      call perform_resets();
      MEDIUM_1$sendCount := MEDIUM_1$sendCount$new - 1;
      MEDIUM_1$sendCount$new := MEDIUM_1$sendCount;
      goto uppaal2boogie$step;
    }
  }
  goto deadlock;
step_ENV_1:
  if (sync == sync_none)
  {
    if (loc$ENV_1 == id31_1)
    {
      goto transition$t45;
transition$t45:
      assume guard_t45(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id30_1;
      ENV_1$t0 := 0.0;
      ENV_1$t0$new := ENV_1$t0;
      ENV_1$t := 0.0;
      ENV_1$t$new := ENV_1$t;
      goto uppaal2boogie$step;
    }
    else    if (loc$ENV_1 == id26_1)
    {
      goto transition$t40;
transition$t40:
      assume guard_t40(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id25_1;
      sync := waiting;
      sync_channel := chan_TX_END;
      sender := ENV_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$ENV_1 == id25_1)
    {
      goto transition$t39;
transition$t39:
      assume guard_t39(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id31_1;
      ENV_1$t := 0.0;
      ENV_1$t$new := ENV_1$t;
      goto uppaal2boogie$step;
    }
    else    if (loc$ENV_1 == id27_1)
    {
      goto transition$t38, transition$t41;
transition$t38:
      assume guard_t38(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id25_1;
      goto uppaal2boogie$step;
transition$t41:
      assume guard_t41(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id26_1;
      call schedule_reset_ENV_1$t0(0.0);
      sync := waiting;
      sync_channel := chan_TX_START;
      sender := ENV_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$ENV_1 == id30_1)
    {
      goto transition$t37, transition$t44;
transition$t37:
      assume guard_t37(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id24_1;
      goto uppaal2boogie$step;
transition$t44:
      assume guard_t44(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id28_1;
      call schedule_reset_ENV_1$t0(0.0);
      sync := waiting;
      sync_channel := chan_TX_START;
      sender := ENV_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$ENV_1 == id24_1)
    {
      goto transition$t36;
transition$t36:
      assume guard_t36(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id31_1;
      ENV_1$t := 0.0;
      ENV_1$t$new := ENV_1$t;
      goto uppaal2boogie$step;
    }
    else    if (loc$ENV_1 == id28_1)
    {
      goto transition$t35;
transition$t35:
      assume guard_t35(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id23_1;
      call schedule_reset_ENV_1$t0(0.0);
      sync := waiting;
      sync_channel := chan_TX_END;
      sender := ENV_1;
      goto step_MEDIUM_1;
    }
    else    if (loc$ENV_1 == id23_1)
    {
      goto transition$t34;
transition$t34:
      assume guard_t34(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id24_1;
      goto uppaal2boogie$step;
    }
  }
  else  if (sync == waiting && sender != ENV_1)
  {
  }
  goto deadlock;
  // *** Broadcast Receivers ***
  // Begin channel COLLISION
broadcast_rcv$COLLISION:
  // Template MAC_1
  if (sender != MAC_1)
  {
    if (loc$MAC_1 == id8_1)
    {
      goto transition$t4, broadcast_rcvr_done$MAC_1$COLLISION$id8_1$negative;
transition$t4:
      assume guard_t4(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id7_1;
      goto broadcast_rcvr_done$COLLISION$MAC_1;
broadcast_rcvr_done$MAC_1$COLLISION$id8_1$negative:
      assume !guard_t4(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
  }
broadcast_rcvr_done$COLLISION$MAC_1:
  // All receivers processed for channel COLLISION
  call perform_resets();
  sync := sync_none;
  goto uppaal2boogie$step;
  // End channel COLLISION
  // Begin channel RX_END
broadcast_rcv$RX_END:
  // Template MAC_1
  if (sender != MAC_1)
  {
    if (loc$MAC_1 == id8_1)
    {
      goto transition$t13, broadcast_rcvr_done$MAC_1$RX_END$id8_1$negative;
transition$t13:
      assume guard_t13(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id6_1;
      call schedule_reset_MAC_1$t0(0.0);
      goto broadcast_rcvr_done$RX_END$MAC_1;
broadcast_rcvr_done$MAC_1$RX_END$id8_1$negative:
      assume !guard_t13(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
    else    if (loc$MAC_1 == id0_1)
    {
      goto transition$t0, broadcast_rcvr_done$MAC_1$RX_END$id0_1$negative;
transition$t0:
      assume guard_t0(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id7_1;
      goto broadcast_rcvr_done$RX_END$MAC_1;
broadcast_rcvr_done$MAC_1$RX_END$id0_1$negative:
      assume !guard_t0(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
  }
broadcast_rcvr_done$RX_END$MAC_1:
  // Template ENV_1
  if (sender != ENV_1)
  {
    if (loc$ENV_1 == id29_1)
    {
      goto transition$t42, broadcast_rcvr_done$ENV_1$RX_END$id29_1$negative;
transition$t42:
      assume guard_t42(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id27_1;
      call schedule_reset_ENV_1$t0(0.0);
      goto broadcast_rcvr_done$RX_END$ENV_1;
broadcast_rcvr_done$ENV_1$RX_END$id29_1$negative:
      assume !guard_t42(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
  }
broadcast_rcvr_done$RX_END$ENV_1:
  // All receivers processed for channel RX_END
  call perform_resets();
  sync := sync_none;
  goto uppaal2boogie$step;
  // End channel RX_END
  // Begin channel RX_START
broadcast_rcv$RX_START:
  // Template MAC_1
  if (sender != MAC_1)
  {
    if (loc$MAC_1 == id10_1)
    {
      goto transition$t16, broadcast_rcvr_done$MAC_1$RX_START$id10_1$negative;
transition$t16:
      assume guard_t16(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id8_1;
      goto broadcast_rcvr_done$RX_START$MAC_1;
broadcast_rcvr_done$MAC_1$RX_START$id10_1$negative:
      assume !guard_t16(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
    else    if (loc$MAC_1 == id9_1)
    {
      goto transition$t10, broadcast_rcvr_done$MAC_1$RX_START$id9_1$negative;
transition$t10:
      assume guard_t10(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id8_1;
      goto broadcast_rcvr_done$RX_START$MAC_1;
broadcast_rcvr_done$MAC_1$RX_START$id9_1$negative:
      assume !guard_t10(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
    else    if (loc$MAC_1 == id3_1)
    {
      goto transition$t6, broadcast_rcvr_done$MAC_1$RX_START$id3_1$negative;
transition$t6:
      assume guard_t6(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$MAC_1 := id0_1;
      goto broadcast_rcvr_done$RX_START$MAC_1;
broadcast_rcvr_done$MAC_1$RX_START$id3_1$negative:
      assume !guard_t6(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
  }
broadcast_rcvr_done$RX_START$MAC_1:
  // Template ENV_1
  if (sender != ENV_1)
  {
    if (loc$ENV_1 == id30_1)
    {
      goto transition$t43, broadcast_rcvr_done$ENV_1$RX_START$id30_1$negative;
transition$t43:
      assume guard_t43(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
      loc$ENV_1 := id29_1;
      goto broadcast_rcvr_done$RX_START$ENV_1;
broadcast_rcvr_done$ENV_1$RX_START$id30_1$negative:
      assume !guard_t43(time,ENV_1$t,MAC_1$t0,APP_LZ_1$t0,ENV_1$t0,MAC_1$t,MEDIUM_1$t0,APP_RX_1$t0,MEDIUM_1$sendCount,channelBusy,queue);
    }
  }
broadcast_rcvr_done$RX_START$ENV_1:
  // All receivers processed for channel RX_START
  call perform_resets();
  sync := sync_none;
  goto uppaal2boogie$step;
  // End channel RX_START
deadlock:
}
