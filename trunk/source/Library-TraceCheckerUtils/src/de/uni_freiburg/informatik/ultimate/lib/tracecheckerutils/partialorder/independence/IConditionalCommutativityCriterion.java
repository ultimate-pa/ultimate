package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;


public interface IConditionalCommutativityCriterion<L extends IAction> {

	
	Boolean decide(IPredicate state, L a, L b);
	
	Boolean decide(IPredicate condition);
}
