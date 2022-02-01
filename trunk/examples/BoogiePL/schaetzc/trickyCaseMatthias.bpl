var a, b : int;

procedure p()
modifies a;
{
   var _v : int;
   a := _v;
}


procedure p_()
modifies b;
{
   var v, v#5, v#2, v#3 : int;
   b := v;
}

