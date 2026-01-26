var flag: int;

procedure ULTIMATE.start()
modifies flag;
{
    flag := 0;
    fork 1 set_flag();
    
    while (flag == 0) { }
    
    assert flag == 1;
}

procedure set_flag()
modifies flag;
{
    flag := 1;
}
