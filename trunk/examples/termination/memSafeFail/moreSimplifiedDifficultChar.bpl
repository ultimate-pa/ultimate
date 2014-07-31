//
implementation cstrcpy(#ins : int, #int : int) returns ()
{
    var s : int;
    var t : int;

    s := #ins;
    t := #int;
    while (true)
    {
	    assert t  < ourLength;
		assert s  < ourLength;
		memory[s] := memory[t];

        if (memory[s] == 0) {
            break;
        } 
        t := t + 1 ;
    }
}



implementation ULTIMATE.start() returns ()
{
    var length : int;
    var string : int;

    assume (length >=0);
	assume ourLength == length + 1;
	assume string == 0;
	assume memory[string + length] == 0;
    call cstrcpy(string, string);
}

var memory : [int]int;

var ourLength : int;

procedure __VERIFIER_nondet_int() returns (#res : int);
    modifies ;

procedure cstrcpy(#ins : int, #int : int) returns ();
    modifies memory;


procedure ULTIMATE.start() returns ();
    modifies memory;
    modifies memory;

