package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

public class ConditionalCommutativityInterpolantProvider<L extends IIcfgTransition<?>> {

	private ConditionalCommutativityChecker<L> mChecker;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAbstraction;

	ConditionalCommutativityInterpolantProvider(IConditionalCommutativityCriterion<L> criterion,
			IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, ITraceChecker<L> traceChecker) {
		mAbstraction = abstraction;
		mChecker = new ConditionalCommutativityChecker<>(criterion, independenceRelation, generator, abstraction,
				emptyStackStateFactory, traceChecker);
	}

	List<IPredicate> getInterpolants(IRun<L, IPredicate> run, List<IPredicate> predicates) {

		for (IPredicate state : run.getStateSequence()) {
			Iterator<OutgoingInternalTransition<L, IPredicate>> iterator =
					mAbstraction.internalSuccessors(state).iterator();

			List<OutgoingInternalTransition<L, IPredicate>> transitions = new ArrayList<>();
			while (iterator.hasNext()) {
				transitions.add(iterator.next());
			}

			for (int j = 0; j < transitions.size(); j++) {
				OutgoingInternalTransition<L, IPredicate> transition1 = transitions.get(j);
				for (int k = j + 1; k < transitions.size(); k++) {
					OutgoingInternalTransition<L, IPredicate> transition2 = transitions.get(k);
					List<IPredicate> conPredicates = mChecker.checkConditionalCommutativity(run, state,
							transition1.getLetter(), transition2.getLetter());
					if (conPredicates != null) {
						predicates.addAll(conPredicates);
					}
				}
			}
		}
		return predicates;
	}

}
