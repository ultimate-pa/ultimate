/*
 * Produces StackOverflowError in 
 *  java.lang.StackOverflowError
 *  	at java.util.HashMap.hash(HashMap.java:338)
 *  	at java.util.HashMap.get(HashMap.java:556)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind.find(UnionFind.java:257)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation.getRepresentative(ThreeValuedEquivalenceRelation.java:232)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation.isRepresentative(ThreeValuedEquivalenceRelation.java:236)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation.getRepresentativesUnequalTo(ThreeValuedEquivalenceRelation.java:340)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.getRepresentativesUnequalTo(CongruenceClosure.java:241)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.doMergeAndComputePropagations(CongruenceClosure.java:224)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.reportEqualityRec(CongruenceClosure.java:165)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.registerNewElement(CongruenceClosure.java:354)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.addElementRec(CongruenceClosure.java:310)
 *  	at java.util.HashMap$KeySpliterator.forEachRemaining(HashMap.java:1548)
 *  	at java.util.stream.ReferencePipeline$Head.forEach(ReferencePipeline.java:580)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.alignElementsAndFunctions(CongruenceClosure.java:721)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.isStrongerThan(CongruenceClosure.java:793)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosureComparator.compare(CongruenceClosureComparator.java:20)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosureComparator.compare(CongruenceClosureComparator.java:1)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils.lambda$0(PosetUtils.java:46)
 *  	at java.util.stream.MatchOps$1MatchSink.accept(MatchOps.java:90)
 *  	at java.util.ArrayList$ArrayListSpliterator.tryAdvance(ArrayList.java:1351)
 *  	at java.util.stream.ReferencePipeline.forEachWithCancel(ReferencePipeline.java:126)
 *  	at java.util.stream.AbstractPipeline.copyIntoWithCancel(AbstractPipeline.java:498)
 *  	at java.util.stream.AbstractPipeline.copyInto(AbstractPipeline.java:485)
 *  	at java.util.stream.AbstractPipeline.wrapAndCopyInto(AbstractPipeline.java:471)
 *  	at java.util.stream.MatchOps$MatchOp.evaluateSequential(MatchOps.java:230)
 *  	at java.util.stream.MatchOps$MatchOp.evaluateSequential(MatchOps.java:196)
 *  	at java.util.stream.AbstractPipeline.evaluate(AbstractPipeline.java:234)
 *  	at java.util.stream.ReferencePipeline.allMatch(ReferencePipeline.java:454)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils.isMaximalElement(PosetUtils.java:46)
 *  	at de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils.lambda$2(PosetUtils.java:64)
 *  	at java.util.stream.ReferencePipeline$2$1.accept(ReferencePipeline.java:174)
 *  	at java.util.ArrayList$ArrayListSpliterator.forEachRemaining(ArrayList.java:1374)
 *  	at java.util.stream.AbstractPipeline.copyInto(AbstractPipeline.java:481)
 *  	at java.util.stream.AbstractPipeline.wrapAndCopyInto(AbstractPipeline.java:471)
 *  	at java.util.stream.ReduceOps$ReduceOp.evaluateSequential(ReduceOps.java:708)
 *  	at java.util.stream.AbstractPipeline.evaluate(AbstractPipeline.java:234)
 *  	at java.util.stream.ReferencePipeline.collect(ReferencePipeline.java:499)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.CCManager.filterRedundantCcs(CCManager.java:81)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph$WeakEquivalenceEdgeLabel.meetRec(WeakEquivalenceGraph.java:1177)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph$WeakEquivalenceEdgeLabel.meet(WeakEquivalenceGraph.java:1159)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph$WeakEquivalenceEdgeLabel.meet(WeakEquivalenceGraph.java:1154)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph.strengthenEdgeLabel(WeakEquivalenceGraph.java:535)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph.reportWeakEquivalence(WeakEquivalenceGraph.java:569)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph.reportWeakEquivalence(WeakEquivalenceGraph.java:576)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeqCongruenceClosure.reportWeakEquivalenceDoOnlyRoweqPropagations(WeqCongruenceClosure.java:295)
 */
int a, b;
int  p1, *p2;

void main() {

        &a;
    p2 = &b;

    b = 1;
    a = 0;

}