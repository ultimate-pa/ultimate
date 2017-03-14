//#Safe

int output = 0;

//@ ltl invariant positive: ( [] ( !(AP(output > 0))));

int main()
{
    while(1)
    {
		output = 0;
    }
}
