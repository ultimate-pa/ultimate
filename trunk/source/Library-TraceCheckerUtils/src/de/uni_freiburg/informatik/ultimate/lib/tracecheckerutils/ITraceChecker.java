package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface ITraceChecker<L extends IIcfgTransition<?>> {

	public boolean checkTrace(IRun<L, IPredicate> run, IPredicate condition);
	
}
