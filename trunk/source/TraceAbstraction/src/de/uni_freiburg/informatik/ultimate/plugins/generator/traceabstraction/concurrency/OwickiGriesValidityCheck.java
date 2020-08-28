package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;

public class OwickiGriesValidityCheck<LETTER, PLACE> {
	private final boolean mIsInductive;
	private final boolean mIsInterferenceFree;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;

	public OwickiGriesValidityCheck(IUltimateServiceProvider services, CfgSmtToolkit csToolkit,
			OwickiGriesAnnotation<LETTER, PLACE> annotation) {
		mPredicateFactory = new BasicPredicateFactory(services, csToolkit.getManagedScript(),
				csToolkit.getSymbolTable());
		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit);

		// TODO Use mPredicateFactory.and(preds)
		// TODO Use mHoareTripleChecker.checkInternal(pre, act, succ)

		mIsInductive = false; // TODO
		mIsInterferenceFree = false; // TODO
	}

	public boolean isValid() {
		return mIsInductive && mIsInterferenceFree;
	}
}
