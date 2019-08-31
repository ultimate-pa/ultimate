//#Safe
/*
 * A program that demonstrates how important Large Block Encoding can be.
 *
 * Author: Elisabeth Schanno (elisabeth.schanno@venus.uni-freiburg.de)
 * Date: 2019-08-31
 * 
 */

var a : int;
var b : int;
var c : int;
var d : int;
var e : int;

var f : bool;


procedure ULTIMATE.start();
modifies a;
modifies b;
modifies c;
modifies d;
modifies e;
modifies f;

implementation ULTIMATE.start()
{
    var x : int;
    x := 23;
    a := 0;
    f := true;

    fork 1 proc1(x);
    fork 2 proc2(x);
    fork 3 proc3(x);
    fork 4 proc4(x);

    join 1 assign a;
    join 2 assign a;
    join 3 assign a;
    join 4 assign a;
    
}

procedure proc1(n : int) returns(res : int);
modifies b;

implementation proc1(n : int) returns(res : int)
{
	assert f == true;
	b := 1;
	b := 1;
	b := 1;
	assert a == 0;
	b := 1;
	b := 1;
	b := 1;
	assert f == true;
	assert f == true;
	res := b;

}


procedure proc2(n : int) returns(res : int);
modifies c;

implementation proc2(n : int) returns(res : int)
{
	assert f == true;
	c := 2;
	c := 2;
	c := c + 2;
        assert a == 0;
	c := a + 2;
	c := 2;
	c := 2;
	assert f == true;
	assert f == true;
	res := c;

}


procedure proc3(n : int) returns(res : int);
modifies d;

implementation proc3(n : int) returns(res : int)
{
	assert f == true;
	d := 3;
	d := 3;
	d := a + 3;
	assert a == 0;
	d := d + 3;
	d := 3;
	d := 3;
	assert f == true;
	assert f == true;
	res := d;

}

procedure proc4(n : int) returns(res : int);
modifies e;

implementation proc4(n : int) returns(res : int)
{
	assert f == true;
	e := 4;
	e := 4;
	e := a + 4;
	assert a == 0;
	e := e + 4;
	e := 4;
	e := 4;
	assert f == true;
	assert f == true;
	res := e;

}

