package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IConditionalCommutativityChecker<L extends IIcfgTransition<?>> {

	boolean checkConditionalCommutativity(IRun<L, IPredicate> run, IPredicate state, L a, L b);
}
