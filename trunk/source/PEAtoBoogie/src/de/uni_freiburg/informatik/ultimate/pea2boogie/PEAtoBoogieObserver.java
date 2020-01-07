package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences.PEATransformerMode;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.Req2BoogieTranslator;
import de.uni_frieburg.informatik.ultimate.pea2boogie.testgen.Req2CauseTrackingPeaTransformer;

public class PEAtoBoogieObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IElement mBoogieAST;
	private PeaResultUtil mReporter;

	public PEAtoBoogieObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof ObjectContainer)) {
			return false;
		}
		@SuppressWarnings("unchecked")
		final List<PatternType> rawPatterns = (List<PatternType>) ((ObjectContainer<?>) root).getValue();

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return false;
		}

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		if(prefs.getEnum(Pea2BoogiePreferences.LABEL_TRANSFOMER_MODE, PEATransformerMode.class) == PEATransformerMode.REQ_CHECK) {
			mReporter = new PeaResultUtil(mLogger, mServices);
			// register CEX transformer that removes program executions from CEX.
			final Function<IResult, IResult> resultTransformer = mReporter::convertTraceAbstractionResult;
			mServices.getResultService().registerTransformer("CexReducer", resultTransformer);
		}

		mBoogieAST = generateBoogie(rawPatterns);

		return false;
	}

	public IElement getResult() {
		return mBoogieAST;
	}

	private IElement generateBoogie(final List<PatternType> patterns) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		if(prefs.getEnum(Pea2BoogiePreferences.LABEL_TRANSFOMER_MODE, PEATransformerMode.class) == PEATransformerMode.REQ_CHECK) {
			return new Req2BoogieTranslator(mServices, mLogger, patterns, new ArrayList<IReq2PeaTransformer>()).getUnit();			
		} else if (prefs.getEnum(Pea2BoogiePreferences.LABEL_TRANSFOMER_MODE, PEATransformerMode.class) == PEATransformerMode.REQ_TEST) {
			return new Req2BoogieTranslator(mServices, mLogger, patterns, Arrays.asList(new Req2CauseTrackingPeaTransformer(mServices, mLogger))).getUnit();
		} else {
			return null;
		}
	}
}
