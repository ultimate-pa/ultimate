//#Safe
// 29.9.2016: The intervall domain does not like multiple constants and sets the post state to top, thus being unable to show safety. 


procedure ULTIMATE.start()
{
  call passParam(3,1);    
  
}                       

procedure passParam(a,b : int) returns ()
{ 
  assert(a == 3);       
}