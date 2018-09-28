package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.Req2BoogieTranslator;

public class PEAtoBoogieObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IElement mBoogieAST;
	private PeaResultUtil mReporter;
	private final IToolchainStorage mStorage;

	public PEAtoBoogieObserver(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		mLogger = logger;
		mServices = services;
		mStorage = storage;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof ObjectContainer)) {
			return false;
		}
		final List<PatternType> rawPatterns = (List<PatternType>) ((ObjectContainer) root).getValue();

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return false;
		}

		mReporter = new PeaResultUtil(mLogger, mServices);
		// register CEX transformer that removes program executions from CEX.
		final Function<IResult, IResult> resultTransformer = mReporter::convertTraceAbstractionResult;
		mServices.getResultService().registerTransformer("CexReducer", resultTransformer);

		mBoogieAST = generateBoogie(rawPatterns);

		return false;
	}

	public IElement getResult() {
		return mBoogieAST;
	}

	private IElement generateBoogie(final List<PatternType> patterns) {
		return new Req2BoogieTranslator(mServices, mStorage, mLogger, patterns).getUnit();
	}
}
