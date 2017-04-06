package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class PredicateQueueResult {
	public final DoubleDecker<IPredicate> mResult;

	public PredicateQueueResult(DoubleDecker<IPredicate> mResult) {
		this.mResult = mResult;
	}
}