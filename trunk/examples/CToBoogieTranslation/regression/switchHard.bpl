implementation main() returns (#res : int){
    var #t~switch0 : bool;
    var #t~switch1 : bool;
    var #t~post2 : int;
    var #t~post3 : int;
    var #t~post4 : int;
    var #t~post5 : int;
    var #t~post6 : int;
    var ~x~1 : int;
    var ~a~1 : int;
    var ~y~1 : int;

    ~x~1 := 1;
    ~a~1 := 0;
    ~y~1 := 0;
    #t~switch0 := ~a~1 == 0;
    if (#t~switch0) {
        assert ~x~1 == 1;
        ~x~1 := 7;
        #t~switch1 := ~x~1 == 7;
        if (#t~switch1) {
            #t~post2 := ~x~1 + 1;
            ~x~1 := #t~post2;
            havoc #t~post2;
            assert ~x~1 == 8;
        }
        #t~switch1 := #t~switch1 || ~x~1 == 4;
        if (#t~switch1) {
            #t~post3 := ~x~1 + 1;
            ~x~1 := #t~post3;
            ~a~1 := #t~post3 + 2143123;
            havoc #t~post3;
            while (true)
            {
              Loop~2:
                #t~post4 := ~y~1 + 1;
                ~y~1 := #t~post4;
                if (!(#t~post4 < 10)) {
                    havoc #t~post4;
                    break;
                } else {
                    havoc #t~post4;
                }
                if (~y~1 > 5) {
                    goto Loop~2;
                }
                ~a~1 := ~a~1 + ~y~1;
                if (~y~1 > 9) {
                    break;
                }
            }
            assert ~y~1 == 10;
            goto SWITCH~BREAK~1;
        }
        #t~switch1 := #t~switch1 || ~x~1 == 5;
        if (#t~switch1) {
            ~a~1 := 0;
            goto SWITCH~BREAK~1;
        }
        #t~switch1 := #t~switch1 || ~x~1 == 6;
        if (#t~switch1) {
        }
        #t~switch1 := #t~switch1 || ~x~1 == 8;
        if (#t~switch1) {
        }
        #t~switch1 := #t~switch1 || true;
        if (#t~switch1) {
            #t~post5 := ~x~1 + 1;
            ~x~1 := #t~post5;
            havoc #t~post5;
        }
      SWITCH~BREAK~1:
        goto SWITCH~BREAK~0;
        goto SWITCH~BREAK~0;
    }
    #t~switch0 := #t~switch0 || ~a~1 == 17;
    if (#t~switch0) {
    }
    #t~switch0 := #t~switch0 || ~a~1 == 1;
    if (#t~switch0) {
        #t~post6 := ~x~1;
        ~x~1 := #t~post6 + 1;
        ~a~1 := #t~post6;
        havoc #t~post6;
        goto SWITCH~BREAK~0;
    }
    #t~switch0 := #t~switch0 || true;
    if (#t~switch0) {
        goto SWITCH~BREAK~0;
    }
  SWITCH~BREAK~0:
    assert ~x~1 == 9;
    assert ~y~1 == 10;
    assert ~a~1 == 2143147;
}

implementation ULTIMATE.init() returns (){
}

implementation ULTIMATE.start() returns (){
    var #t~ret7 : int;

    call ULTIMATE.init();
    call #t~ret7 := main();
}

procedure main() returns (#res : int);
modifies ;

procedure ULTIMATE.init() returns ();
modifies ;
modifies ;

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

