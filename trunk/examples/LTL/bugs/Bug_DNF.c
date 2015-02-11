//#Safe

//@ ltl invariant positive: ( []<> ( AP(input == 3)));

int input;

int main()
{
	input = 5;

    while(1)
    {
		if(input==0 || input==1 || input==2 || input ==4){
			input=input+1;
		} else {
			input=input-3;
		}
    }
}
