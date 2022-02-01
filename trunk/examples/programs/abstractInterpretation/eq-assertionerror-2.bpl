//#Safe 
/*
 * java.lang.AssertionError
 * 	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.elementIsFullyRemovedOnlyCc(CongruenceClosure.java:679)
 * 	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.removeAnyElement(CongruenceClosure.java:497)
 * 	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.removeAnyElement(CongruenceClosure.java:492)
 * 	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.removeSimpleElementTrackNewReps(CongruenceClosure.java:451)
 * 	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeqCongruenceClosure.removeSimpleElement(WeqCongruenceClosure.java:778)
 * 	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint.removeElement(EqConstraint.java:384)
 * 	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory.projectExistentially(EqConstraintFactory.java:332)
 * 	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint.lambda$2(EqDisjunctiveConstraint.java:93)
 * 	at java.util.stream.ReferencePipeline$3$1.accept(ReferencePipeline.java:193)
 */

type $Pointer$ = { base : int, offset : int };

var #NULL : $Pointer$;
var #valid : [int]int;
var #length : [int]int;
var #memory_int : [$Pointer$]int;

procedure ULTIMATE.init() returns ()
modifies #valid, #NULL;
modifies ;
{
    #NULL := { base: 0, offset: 0 };
    #valid[0] := 0;
}

procedure ULTIMATE.start() returns ()
modifies #valid, #NULL, #memory_int;
modifies #valid, #length, #memory_int;
{
    call ULTIMATE.init();
    call main();
}

procedure mutex_lock(#in~a : int) returns ()
modifies ;
{

}

procedure main() returns ()
modifies #memory_int, #valid, #length;
{
    var p : $Pointer$;

    call p := #Ultimate.alloc(4);
    call write~int(0, { base: p!base, offset: p!offset + 0 }, 4);
    call mutex_lock(p!base + p!offset);
    call ULTIMATE.dealloc(p);
    havoc p;
}



procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
modifies #memory_int;
ensures true && #memory_int == old(#memory_int)[#ptr := #value];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
ensures #value == #memory_int[#ptr];

procedure ULTIMATE.free(~addr : $Pointer$) returns ();
free requires ~addr!offset == 0;
free requires ~addr!base == 0 || #valid[~addr!base] == 1;
free ensures (if ~addr!base == 0 then #valid == old(#valid) else #valid == old(#valid)[~addr!base := 0]);
modifies #valid;

procedure ULTIMATE.dealloc(~addr : $Pointer$) returns ();
free ensures #valid == old(#valid)[~addr!base := 0];
modifies #valid;

procedure #Ultimate.alloc(~size : int) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == 0;
ensures #valid == old(#valid)[#res!base := 1];
ensures #res!offset == 0;
ensures #res!base != 0;
ensures #length == old(#length)[#res!base := ~size];
modifies #valid, #length;

