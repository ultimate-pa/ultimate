// ltl invariant positive: (AP(p == 1) R (AP(p == 0) || AP(p == 1) ));
// ltl invariant positive: (AP(p == 0) U AP(p == 1) );
//@ ltl invariant positive: <> AP(p == 1) ;

/*

let rec halt _ = 
	and shrink f  
	if (f() =0 ) then 
		halt()
	else shrink (lambda_ . f() -1) 

and main()
	let t = *+ in shrink (lambda_. t)
*/

extern int __VERIFIER_nondet_int();

int x;
int p;

int shrink(){
	if(x == 0){
		while(1){
			p=1;
		}
	} 
	x = x-1;
	shrink();
}

int main()
{
	x = __VERIFIER_nondet_int();
	p = 0;
	if(x<0){
		p=1;
		return;
	}
	shrink();

}


