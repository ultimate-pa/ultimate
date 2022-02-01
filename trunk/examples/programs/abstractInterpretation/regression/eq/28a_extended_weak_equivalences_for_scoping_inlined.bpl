//#Safe	
/*
 * (is safe because there is no specification)
 * Triggers "post is unsound" assertion failure on equality domain as of 6.11.2017.
 */
var valid : [int]bool;

procedure foo() returns ();
modifies valid;

implementation foo() returns (){
    var q : int;
    var malloc_old_valid : [int]bool;

    malloc_old_valid := valid;
    havoc valid;
    assume malloc_old_valid[q] == false;
    assume valid == malloc_old_valid[q := true];
}

procedure main() returns ();
modifies valid;

implementation main() returns (){
    var p : int;
    var malloc_old_valid : [int]bool;

    malloc_old_valid := valid;
    havoc valid;
    assume malloc_old_valid[p] == false;
    assume valid == malloc_old_valid[p := true];

    call foo();
}

