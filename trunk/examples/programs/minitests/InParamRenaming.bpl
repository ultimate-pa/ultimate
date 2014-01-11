//#Safe
implementation method1(a:int, b:int) returns (#res:int)
{
 var #in~a : int;
 var #in~b : int;
 #in~a := a;
 #in~b := b;
 if (#in~a > #in~b) {
 #res := #in~a - #in~b;
 return;
 } else {
 #res := #in~b - #in~a;
 return;
 }
}
implementation method2(c:int, d:int) returns (#res:int)
{
 var #in~c : int;
 var #in~d : int;
 var #t~CALL~0 : int;
 #in~c := c;
 #in~d := d;
 call #t~CALL~0 := method1(#in~c, #in~d);
 #res := #in~c + #in~d + #t~CALL~0;
 return;
}
implementation main() returns (#res:int)
{
 var #t~CALL~1 : int;
 call #t~CALL~1 := method2(10, 11);
}
procedure method2(unnamed~921557776:int, named1:int) returns (#res:int);
 requires named1 > 0;
 modifies ;
procedure main() returns (#res:int);
 modifies ;
procedure method1(unnamed~1610418971:int, unnamed~1575242456:int) returns (#res:int);
 modifies ;
procedure ~init() returns ();
 modifies ;
implementation ~init() returns ()
{
}
