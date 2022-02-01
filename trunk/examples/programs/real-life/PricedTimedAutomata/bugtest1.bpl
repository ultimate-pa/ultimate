//#Unsafe
var power: real;
var x : real;

function { :inline true } property (power:real, x:real) returns (bool)
{ power <= 1000.0 }

procedure main () returns ()
modifies power, x;
requires x == 0.0;
{
var delay : real;
power := 0.0;
step:
assert property(power,x);
havoc delay;
assume delay >= 0.0;
x := x + delay;
power := power + delay * 100.0;
// invariant
assume x <= 10.0;
assert property(power,x);
// guard
assume x >= 10.0;
x := 0.0;
goto step;
}