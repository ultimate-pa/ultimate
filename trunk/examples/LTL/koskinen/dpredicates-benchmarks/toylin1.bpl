// Based on benchmark toylin1.c
// manually translated by DD
//
// #LTLProperty: x U (!x && (a -> <>b))
// #IRS: a: c > 5
// #IRS: b: resp > 5
// #IRS: x: init = 0
// 
// Property should hold 
// 
// Additional comments: 
// * init is new and necessary to state that the property should only be analysed after init 
// * ULTIMATE.start() replaced an empty main() method 

var c,servers,resp,curr_serv : int;
var init : int;

procedure init() 
modifies c,servers,resp,curr_serv;
{
  havoc c;
  assume(c>0);
  servers := 4;
  resp := 0;
  curr_serv := servers;
}

procedure body() 
modifies c,resp,curr_serv;
{
  var ddd : int;
  while(curr_serv > 0) {
    if(*) {
      c := c - 1; 
	  curr_serv := curr_serv - 1;
      resp := resp + 1;
    } else {
      assume(c < curr_serv);
      curr_serv := curr_serv - 1;
    }
  }
  while(true) { ddd:=ddd; }
}

procedure ULTIMATE.start() 
modifies c,servers,resp,curr_serv,init;
{
	init := 0;
	call init();
	init := 1;
	call body();
}