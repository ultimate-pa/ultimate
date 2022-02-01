//#Unsafe
/*
 * AssertionError: Sequence of interpolants not inductive!
 * Bug in AbsIntHTC 
 * Minimal example 
 */


var ~methAndRunningLastTime : int;
var ~pumpRunning : int;


procedure ULTIMATE.init() returns ()
modifies ~methAndRunningLastTime, ~pumpRunning;
{
    ~methAndRunningLastTime := 0;
    ~pumpRunning := 0;
}

procedure ULTIMATE.start() returns ()
modifies ~methAndRunningLastTime, ~pumpRunning;
{
    call ULTIMATE.init();
    call main();
}


implementation __utac_acc__Specification2_spec__2() returns (){
    if (~methAndRunningLastTime != 0) {
        assert false;
    } else {
        ~methAndRunningLastTime := 1;
    }
}

implementation timeShift() returns (){
    call processEnvironment();
    call __utac_acc__Specification2_spec__2();
}

implementation processEnvironment__wrappee__highWaterSensor() returns (){
    call activatePump();
}

implementation processEnvironment() returns (){
    var ~tmp~9 : int;

    havoc ~tmp~9;
    if (~pumpRunning != 0) {
        call processEnvironment__wrappee__highWaterSensor();
    }
}

implementation activatePump() returns (){
    ~pumpRunning := 0;
}

implementation test() returns (){
    call cleanup();
}

implementation cleanup() returns (){
    var ~i~13 : int;

    havoc ~i~13;
    call timeShift();
    ~i~13 := 0;
    if (~i~13 < 0) {
    }
    call timeShift();
}

implementation main() returns (){
    call test();
}



procedure activatePump() returns ();
modifies ~pumpRunning;

procedure processEnvironment() returns ();
modifies ~pumpRunning;

procedure cleanup() returns ();
modifies ~methAndRunningLastTime, ~pumpRunning;

procedure __utac_acc__Specification2_spec__2() returns ();
modifies ~methAndRunningLastTime;

procedure timeShift() returns ();
modifies ~methAndRunningLastTime, ~pumpRunning;

procedure processEnvironment__wrappee__highWaterSensor() returns ();
modifies ~pumpRunning;

procedure test() returns ();
modifies ~methAndRunningLastTime, ~pumpRunning;

procedure main() returns ();
modifies ~methAndRunningLastTime, ~pumpRunning;






