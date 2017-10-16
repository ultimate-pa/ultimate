procedure foo() returns(){
	assert false;
}

procedure main() returns (){
    while (true)
    {
        if (true) {
            break;
        }
        while (true)
        {
            if (true) {
                break;
            }
            call foo();
        }
        call foo();
    }
}