//#Safe
/*
 * DD 2017-06-08
 * This program is reported as unsafe because Ultimate does not respect static const. 
 */
 
static const int x=1;

int some_function() 
{ 
	if(x!=1){
		//@assert 0;
	}
}
