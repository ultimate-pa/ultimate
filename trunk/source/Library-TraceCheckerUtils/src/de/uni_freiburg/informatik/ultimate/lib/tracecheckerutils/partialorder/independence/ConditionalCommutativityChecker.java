package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;

public class ConditionalCommutativityChecker<L extends IIcfgTransition<?>>
		implements IConditionalCommutativityChecker<L> {

	private IConditionalCommutativityCriterion<L> mCriterion;
	private SemanticIndependenceConditionGenerator mGenerator;
	private ITraceChecker<L> mTraceChecker;

	public ConditionalCommutativityChecker(IConditionalCommutativityCriterion<L> criterion,
			IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator,
			final IAutomaton<L, IPredicate> abstraction, IEmptyStackStateFactory<IPredicate> emptyStackStateFactory,
			ITraceChecker<L> traceChecker) {
		mCriterion = criterion;
		mGenerator = generator;
		mTraceChecker = traceChecker;

	}

	@Override
	public List<IPredicate> checkConditionalCommutativity(IRun<L, IPredicate> run, IPredicate state, L a, L b) {

		if (mCriterion.decide(state, a, b)) {
			IPredicate condition = mGenerator.generateCondition(state, a.getTransformula(), b.getTransformula());
			if (mCriterion.decide(condition)) {
				return mTraceChecker.checkTrace(run, condition);
			}
		}
		return null;
	}
}
