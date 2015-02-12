//#Safe

//@ ltl invariant positive: <> AP(input == 3) || <> AP(input == 4);

int input;
int nutzlos;

void bar(int *k, int i)
{
	(*k)=(*k)+i;
}

void foo(){
	if(input==0 || input==1 || input==2 || input ==4){
		bar(&nutzlos,1);
		input = input + 1;
	} else {
		bar(&nutzlos,-3);
		input = input - 3;
	}
}

int main()
{
	nutzlos = 0;
	input = 5;
	bar(&nutzlos,5);
	
    while(1)
    {
		foo();
	}
}

