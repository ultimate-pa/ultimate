package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IConditionalCommutativityCriterion<L extends IIcfgTransition<?>> {

	boolean decide(IPredicate state, L a, L b);

	boolean decide(IPredicate condition);

}
