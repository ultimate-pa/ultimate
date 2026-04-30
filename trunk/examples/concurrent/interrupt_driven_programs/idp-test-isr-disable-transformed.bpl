implementation ULTIMATE.init() returns (){
    ~button_state~0 := 0;
    ~step_in_isr~0 := 0;
    ~isr_executed~0 := 0;
    #isr_1_enabled := false;
}

implementation ULTIMATE.start() returns (){
    var #t~ret2 : int;

    call ULTIMATE.init();
    call #t~ret2 := main();
}

implementation main() returns (#res : int){
    var #t~post0 : int;
    var ~n~0 : int;

    fork -1 #isr_1_isr_gpio_thr();
    call HAL_GPIO_Init();
    call HAL_GPIO_Enable_Int();
    ~n~0 := 0;
    while (~n~0 < 1000)
    {
        assert { :reach "ASSERT","assert" } 0 == ~step_in_isr~0 % 256;
        #t~post0 := ~n~0;
        ~n~0 := 1 + #t~post0;
        havoc #t~post0;
        assert { :reach "ASSERT","assert" } 0 == ~step_in_isr~0 % 256;
    }
    call HAL_GPIO_Disable_Int();
    ~isr_executed~0 := 0;
    assert { :reach "ASSERT","assert" } 0 != ~isr_executed~0 % 256;
    #res := 0;
    return;
}

implementation HAL_GPIO_Enable_Int() returns (){
    atomic {
        #isr_1_enabled := true;
    }
}

implementation HAL_GPIO_Disable_Int() returns (){
    atomic {
        #isr_1_enabled := false;
    }
}

implementation isr_gpio() returns (){
    var #t~ret1 : int;
    var ~st~0 : int;

    ~step_in_isr~0 := 1;
    call #t~ret1 := HAL_GPIO_Read();
    ~st~0 := (if 0 == #t~ret1 % 256 then 0 else 1);
    havoc #t~ret1;
    if (1 == ~st~0 % 256) {
        call HAL_GPIO_Write(10, 1);
        ~button_state~0 := (if 0 == ~st~0 % 256 then 0 else 1);
    } else {
        call HAL_GPIO_Write(10, 0);
        ~button_state~0 := (if 0 == ~st~0 % 256 then 0 else 1);
    }
    ~step_in_isr~0 := 0;
    ~isr_executed~0 := 1;
}

implementation #isr_1_isr_gpio_thr() returns (){
    while (true)
    {
        atomic {
            if (#isr_1_enabled) {
                call isr_gpio();
            }
        }
    }
}

var #isr_1_enabled : bool;

var ~button_state~0 : int;

var ~step_in_isr~0 : int;

var ~isr_executed~0 : int;

type $Pointer$ = { base : int };
procedure HAL_GPIO_Init() returns ();
modifies ;

procedure HAL_GPIO_Enable_Int() returns ();
modifies #isr_1_enabled;

procedure HAL_GPIO_Disable_Int() returns ();
modifies #isr_1_enabled;

procedure isr_gpio() returns ();
modifies ~step_in_isr~0, ~button_state~0, ~isr_executed~0;

procedure HAL_GPIO_Read() returns (#res : int);
modifies ;

procedure HAL_GPIO_Write(#in~pin : int, #in~state : int) returns ();
modifies ;

procedure main() returns (#res : int);
modifies ~isr_executed~0, #isr_1_enabled, ~step_in_isr~0, ~button_state~0;

procedure #isr_1_isr_gpio_thr() returns ();
modifies ~step_in_isr~0, ~button_state~0, ~isr_executed~0;

procedure ULTIMATE.init() returns ();
modifies ~button_state~0, ~step_in_isr~0, ~isr_executed~0, #isr_1_enabled;

procedure ULTIMATE.start() returns ();
modifies ~button_state~0, ~step_in_isr~0, ~isr_executed~0, #isr_1_enabled;

