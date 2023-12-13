package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IConditionalCommutativityChecker<L extends IIcfgTransition<?>> {

	List<IPredicate> checkConditionalCommutativity(IRun<L, IPredicate> run, IPredicate state, L a, L b);

}
