package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class FastUprCore {

	private final Term mRelation;
	private final UnmodifiableTransFormula mFormula;
	private final UnmodifiableTransFormula mResult;
	private final ILogger mLogger;
	ReplacementVarFactory mReplacementVarFactory;
	ManagedScript mManagedScript;
	IUltimateServiceProvider mServices;

	public FastUprCore(final UnmodifiableTransFormula formula, final ReplacementVarFactory factory,
			final ManagedScript managedScript, final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mFormula = formula;
		mRelation = formula.getFormula();
		mResult = prefixLoop();
		mServices = services;
	}

	private UnmodifiableTransFormula prefixLoop() {
		int b = 0;
		final boolean resultFound = false;
		while (!resultFound) {
			periodLoop(b++);
		}

		return null;
	}

	private void periodLoop(final int b) {
		for (int c = 0; c <= b; c++) {
			final ConsistencyChecker checker =
					new ConsistencyChecker(mLogger, mManagedScript, mServices, mFormula, b, c);
			if (checker.isSuccess()) {
				checker.getResult();
				return;
			}

		}
	}
}
