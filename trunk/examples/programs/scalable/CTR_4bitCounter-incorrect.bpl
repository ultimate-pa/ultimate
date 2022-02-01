//#Unsafe
procedure Counter () 
{
var x0, x1, x2, x3 : int;

x0 := 0;
x1 := 0;
x2 := 0;
x3 := 0;

while(x3 == 0) {
if ( x0 == 0) { x0 := 1; }
else {
x0 := 0;
if ( x1 == 0) { x1 := 1; }
else {
x1 := 0;
if ( x2 == 0) { x2 := 1; }
else {
x2 := 0;
if ( x3 == 0) { x3 := 1; }
else {
x3 := 0;
}
}
}
}
}
assert (x0 == 0 && x1 == 0 && x2 == 0 && x3 == 0);

}
