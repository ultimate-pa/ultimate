//#Unsafe
/*
	28.4.2017 
	Old Statement Bug in Abstract interpretation 
	Old value not carried over by octagons 

*/ 

var ~sent_encrypted : int;

procedure ULTIMATE.init() returns ()
modifies ~sent_encrypted;
{
    ~sent_encrypted := 0;
}

procedure ULTIMATE.start() returns ()
modifies ~sent_encrypted;
{
    call ULTIMATE.init();
    call main();
}

procedure fooG() returns ()
modifies ~sent_encrypted;
{
    ~sent_encrypted := 1;
}

procedure fooI() returns (){
    call __automaton_fail();
}

procedure fooF() returns ()
modifies ~sent_encrypted;
{
    call fooG();
    call fooH();
}

procedure fooE() returns ()
modifies ~sent_encrypted;
{
    call fooF();
}

procedure fooD() returns ()
modifies ~sent_encrypted;
{
    call fooE();
}

procedure fooC() returns ()
modifies ~sent_encrypted;
{
    call fooD();
}

procedure fooB() returns ()
modifies ~sent_encrypted;
{
    call fooC();
}

procedure fooH() returns (){
    call fooI();
}

procedure __automaton_fail() returns (){
  ERROR:
    assert false;
}

procedure fooA() returns ()
modifies ~sent_encrypted;
{
    call fooB();
}

procedure main() returns ()
modifies ~sent_encrypted;
{
    call test();
}

procedure test() returns ()
modifies ~sent_encrypted;
{

    var i : int;
    i := 0;
    while (true)
    {
        if (i < 4) {
        } else {
            call fooA();
			return;
        }
        i := i + 1;
    }
}
