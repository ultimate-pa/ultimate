implementation main() returns (#res : int){
    if (~e_tag~a == 0) {
        assert false;
    }
}

const ~e_tag~a : int;
const ~e_tag~b : int;
const ~e_tag~c : int;
const ~e_tag~d : int;
const ~e_tag~e : int;
const ~e_tag~f : int;
const ~e_tag~g : int;
const ~e_tag~h : int;
var ~var : int;

axiom ~e_tag~a == 0;
axiom ~e_tag~b == 1;
axiom ~e_tag~c == 2;
axiom ~e_tag~d == 20;
axiom ~e_tag~e == 21;
axiom ~e_tag~f == 22;
axiom ~e_tag~g == 20;
axiom ~e_tag~h == 21;
implementation ULTIMATE.init() returns (){
    ~var := 0;
}

implementation ULTIMATE.start() returns (){
    var #t~ret0 : int;

    call ULTIMATE.init();
    call #t~ret0 := main();
}

procedure main() returns (#res : int);
modifies ;

procedure ULTIMATE.init() returns ();
modifies ~var;
modifies ;

procedure ULTIMATE.start() returns ();
modifies ~var;
modifies ;

