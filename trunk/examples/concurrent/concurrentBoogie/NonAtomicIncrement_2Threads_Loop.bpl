/*
 * 
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-08-23
 * 
 */

var x : int;

procedure ULTIMATE.start();
modifies x;

implementation ULTIMATE.start()
{
    var x : int;
    var y : bool;
    x := 0;

    fork 1 fistIncrementProcess();
	fork 2 secondIncrementProcess();
    join 1;
	join 2;
	assert x >= 2;
}

procedure fistIncrementProcess();
modifies x;

implementation fistIncrementProcess()
{
	var localx : int;
	var i : int;
	i := 0;
	while (i < 5) {
		localx := x;
		x := localx + 1;
		i := i + 1;
	}
}


procedure secondIncrementProcess();
modifies x;

implementation secondIncrementProcess()
{
	var localx : int;
	var i : int;
	i := 0;
	while (i < 5) {
		localx := x;
		x := localx + 1;
		i := i + 1;
	}
}
