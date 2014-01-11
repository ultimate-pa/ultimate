//#Safe
procedure Counter () 
{
var x0, x1, x2, x3, x4, x5, x6, x7 : int;

x0 := 0;
x1 := 0;
x2 := 0;
x3 := 0;
x4 := 0;
x5 := 0;
x6 := 0;
x7 := 0;

while(x7 == 0) {
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
if ( x4 == 0) { x4 := 1; }
else {
x4 := 0;
if ( x5 == 0) { x5 := 1; }
else {
x5 := 0;
if ( x6 == 0) { x6 := 1; }
else {
x6 := 0;
if ( x7 == 0) { x7 := 1; }
else {
x7 := 0;
}
}
}
}
}
}
}
}
}
assert (x0 == 0 && x1 == 0 && x2 == 0 && x3 == 0 && x4 == 0 && x5 == 0 && x6 == 0 && x7 == 1);

}
