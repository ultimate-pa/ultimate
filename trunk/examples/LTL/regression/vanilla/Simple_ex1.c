//#Safe
//@ ltl invariant positive: AP(x>0) U AP(x==0);

int x = 0;

int main()
{
	x = 10;
    while(x>0)
    {
		x--;
    }
}
