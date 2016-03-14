//#Unsafe
var time: real;
var power: real;

procedure main() returns ()
	modifies time, power;
{
	var delay : real;
	time := 0.0;
	power := 0.0;
	while (time < 50.0) {
		havoc delay;
		assume delay >= 0.0 && delay <= 1.0;
		time := time + delay;
		power := power + delay * 2.0;
		assert power < 100.0;
	}
}