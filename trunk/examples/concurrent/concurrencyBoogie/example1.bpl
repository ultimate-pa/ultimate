/*
 * Just a little example to demonstrate how the fork and join statements can 
 * be used.
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 09.05.2018
 * 
 */

var n: int;

procedure Main();
modifies n;

implementation Main()
{
    var x := int;
    x := 4;
    fork 1 foo();
    fork 2 foo();
    
    n := 2;
    
    join x;
    x := 4;
    join x;
}

procedure foo();
modifies n;

implementation foo()
{
    n := 1;
}

procedure bar();
modifies n;

implementation bar()
{
    n := 2;    
}