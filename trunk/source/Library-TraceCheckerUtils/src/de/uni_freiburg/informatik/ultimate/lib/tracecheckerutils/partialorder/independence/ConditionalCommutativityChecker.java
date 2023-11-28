package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;


public class ConditionalCommutativityChecker<L extends IAction> {

	public ConditionalCommutativityChecker(IRun<L, IPredicate> run, IPredicate state, L a, L b, IConditionalCommutativityCriterion<L> criterion,
			IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator) {
		
		if (Boolean.TRUE.equals(criterion.decide(state, a, b))) {
			IPredicate condition = generator.generateCondition(state, a.getTransformula(), b.getTransformula());
			if (Boolean.TRUE.equals(criterion.decide(condition))) {
				//check if run + \neg condition is infeasible
			}
		}
	}
}
