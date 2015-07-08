implementation main() returns (#res : int){
    var ~x~1 : ~mytypex;
    var ~y~1 : int;

    ~x~1 := ~xxx~A;
    ~y~1 := ~xxx~B;
    #res := 0;
    return;
}

const ~xxx~A : int;
const ~xxx~B : int;
const ~xxx~C : int;
type ~mytypex = int;
axiom ~xxx~A == 0;
axiom ~xxx~B == 1;
axiom ~xxx~C == 2;
implementation ULTIMATE.init() returns (){
}

implementation ULTIMATE.start() returns (){
    var #t~ret0 : int;

    call ULTIMATE.init();
    call #t~ret0 := main();
}

procedure main() returns (#res : int);
modifies ;

procedure ULTIMATE.init() returns ();
modifies ;
modifies ;

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

