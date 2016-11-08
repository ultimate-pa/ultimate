//#Unsafe
/* 
 * author nutz 
 * this shows the unsoundness of our emtiness check via bfs in early oct 12
 * (the problem is that "hasBeenExpanded" only looks at the pair <Location, preCallNode>
 *  and terminates if this combination already occurs on the current path. This example
 *  has an error path with two identical pairs of this type.)
 */

var g: int;

procedure main();
modifies g;

implementation main()
{
  g:= 0;
  call u();
  assert g != 3;
}

procedure u() returns ();
modifies g;

implementation u() returns ()
{
  g:=g+1;
  if (g <= 2) {
    call u();
  }
}
 
