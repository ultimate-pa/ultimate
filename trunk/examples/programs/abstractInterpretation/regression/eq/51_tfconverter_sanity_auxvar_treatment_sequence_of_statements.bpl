//#Safe
/*
 * Lead to a report of an unsound Transformula->EqConstraint translation with 
 * setting "SequenceOfStatements".
 * (Problem was: the auxvars were named differently in tf.getClosedFormula, 
 *  and the Term we built from the EqConstraint.)
 */

var valid : [int]bool;

procedure main() returns ();
modifies valid;

implementation main() returns (){
    var p : int;
    var malloc_old_valid : [int]bool;

    malloc_old_valid := valid;
    havoc valid;

    valid[p] := true;
}

