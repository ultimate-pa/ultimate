//#Safe
// 29.9.2016: 
// The non-relational post operator fails to handle passing multiple constants correctly. 
// Instead, it sets the post state to top.


procedure ULTIMATE.start()
{
  call passParam(3,0);    
}                       

procedure passParam(a, b : int) returns ()
{ 
  assert(b == 0);
}