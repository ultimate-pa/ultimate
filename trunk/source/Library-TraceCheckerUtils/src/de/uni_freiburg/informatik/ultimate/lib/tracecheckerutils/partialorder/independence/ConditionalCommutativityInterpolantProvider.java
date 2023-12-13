package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

public class ConditionalCommutativityInterpolantProvider<L extends IIcfgTransition<?>> {
	
	private ConditionalCommutativityChecker<L> mChecker;

	ConditionalCommutativityInterpolantProvider(IConditionalCommutativityCriterion<L> criterion, IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator,
			final IAutomaton<L, IPredicate> abstraction, IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, ITraceChecker<L> traceChecker){
		mChecker = new ConditionalCommutativityChecker<>(criterion, independenceRelation, generator, abstraction, emptyStackStateFactory, traceChecker);
	}
	
	List<IPredicate> getInterpolants(IRun<L, IPredicate> run, List<IPredicate> predicates){	
		
		List<IPredicate> stateSequence = run.getStateSequence();
		for(int i = 0; i < (run.getLength()-1); i++) {
			IPredicate state = stateSequence.get(i);
			List<IcfgEdge> edges = run.getSymbol(i).getSource().getOutgoingEdges();
			
			for (int j = 0; j < edges.size(); j++) {
			    IcfgEdge edge1 = edges.get(j);
			    for (int k = j + 1; k < edges.size(); k++) {
			        IcfgEdge edge2 = edges.get(k);
			        List<IPredicate> conPredicates = mChecker.checkConditionalCommutativity(run, state, (L) edge1, (L) edge2);
			        if (conPredicates != null) {
				        predicates.addAll(conPredicates);
			        }
			    }
			}
		}
		return predicates;		
	}

}
