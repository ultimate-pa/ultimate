// #Safe
/* 
 * Simplified and slightly modified variant of 
 * BugLiveVariables03-Safe.bpl
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-01-03
 *
 */

implementation main() returns (){
    var arr : int;
    var p : int;
    var i : int;

    call arr := malloc(true);

    assume (arr != 0);
    call p := malloc(true);
    call write~$Pointer$(arr, 0);
    call p := malloc(true);
    i := 1;
    call write~$Pointer$(arr, i);
    return;
}

procedure malloc(size : bool) returns (res.base : int)
modifies #valid, #length;
{
    call res.base := #Ultimate.alloc((if size then 39 else -17));
}

var #valid : [int]int;
var #length : [int]int;

procedure write~$Pointer$(#ptr.base : int, #ptr.offset : int) returns ();
requires #ptr.offset <= #length[#ptr.base];

procedure #Ultimate.alloc(size : int) returns (res.base : int);
free ensures old(#valid)[res.base] == 0;
free ensures #valid == old(#valid)[res.base := 1];
// free ensures res.base != 0;
free ensures #length == old(#length)[res.base := size];
modifies #valid, #length;


procedure main() returns ();
modifies #valid, #length;

