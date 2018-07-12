package de.uni_freiburg.informatik.ultimate.reqtotest;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class ReqToTestObserver extends BaseObserver{

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IElement mBoogieAST;
	private final IToolchainStorage mStorage;


	public ReqToTestObserver(final ILogger logger, final IUltimateServiceProvider services,
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
		final ReqSymbolExpressionTable symbolExpressionsTable = 
				new ReqToDeclarations(mLogger).patternListToBuechi(rawPatterns);
		final ReqToBuchi reqToBuchi = new ReqToBuchi(mLogger, mServices, mStorage, symbolExpressionsTable);
		final List<ReqGuardGraph<String>> automata = reqToBuchi.patternListToBuechi(rawPatterns);


		return false;
	}


}
