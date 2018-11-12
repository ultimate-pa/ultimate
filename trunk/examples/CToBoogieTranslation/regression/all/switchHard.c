int main() {
	int x = 1;
	int a = 0;
	int y = 0;
	switch(a) {
        --x; // Should not make an affect
		case 0: // matches
			{
                //@ assert x == 1;
                x = 7; 
                switch (x) {
                    case 7: ++x; //matches
                    //@ assert x == 8;
                    case 4: { //matches because of case 7
                        a = (++x) + 2143123;
                        while(++y < 10) {
                            if (y > 5)
                                continue; // Goto statement to the end of the loop.
                            a += y;
                            if (y > 9)
                                break; // Break statement for the loop
                        }
                        //@ assert y == 10;
                        break; // Goto the end of the 2nd switch.
                    }
                    // not reached
                    case 5: a = 0; break; // breaks the second switch
                    case 6:
                    case 8:
                    default: ++x;
                }
                break; // breaks the first switch
			}
        // unreached
            break; // breakes the first switch

        case 17:

		case 1:  {a = x++;}
                 break;

        default: break;
	}
    //@ assert x == 9;
    //@ assert y == 10;
    //@ assert a == 2143147;
}
