package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

public class OwickiGriesValidityCheck<LETTER, PLACE> {
	private final boolean mIsInductive;
	private final boolean mIsInterferenceFree;

	public OwickiGriesValidityCheck(OwickiGriesAnnotation<LETTER, PLACE> annotation, IPredicateUnifier unifier,
			IHoareTripleChecker htc) {
		mIsInductive = false; // TODO
		mIsInterferenceFree = false; // TODO

		// TODO Use unifier.getOrConstructPredicateForConjunction(Collection<IPredicate>)
		// TODO Use htc.checkInternal(pre, act, succ)
	}

	public boolean isValid() {
		return mIsInductive && mIsInterferenceFree;
	}
}
