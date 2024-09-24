package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.Collections;
import java.util.List;
import java.util.function.UnaryOperator;

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
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.Req2CauseTrackingPeaTransformer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqTestResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.RedundancyTransformer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.Req2BoogieTranslator;

public class PEAtoBoogieObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IElement mBoogieAST;

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
		final List<PatternType<?>> rawPatterns = (List<PatternType<?>>) ((ObjectContainer<?>) root).getValue();

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return false;
		}
		mBoogieAST = generateBoogie(rawPatterns);
		return false;
	}

	public IElement getResult() {
		return mBoogieAST;
	}

	private IElement generateBoogie(final List<PatternType<?>> patterns) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final PEATransformerMode mode =
				prefs.getEnum(Pea2BoogiePreferences.LABEL_TRANSFOMER_MODE, PEATransformerMode.class);
		if (mode == PEATransformerMode.REQ_CHECK) {
			return generateReqCheckBoogie(patterns);
		}
		if (mode == PEATransformerMode.REQ_TEST) {
			return generateReqTestBoogie(patterns);
		}
		if (mode == PEATransformerMode.REQ_RED) {
			return generateReqCheckRedundancyBoogie(patterns);
		}
		return null;
	}

	private IElement generateReqCheckBoogie(final List<PatternType<?>> patterns) {
		final Req2BoogieTranslator translator =
				new Req2BoogieTranslator(mServices, mLogger, patterns, Collections.emptyList());
		final VerificationResultTransformer reporter =
				new VerificationResultTransformer(mLogger, mServices, translator.getReqSymbolTable());
		// register CEX transformer that removes program executions from CEX.
		final UnaryOperator<IResult> resultTransformer = reporter::convertTraceAbstractionResult;
		mServices.getResultService().registerTransformer("CexReducer", resultTransformer);
		return translator.getUnit();
	}

	private IElement generateReqTestBoogie(final List<PatternType<?>> patterns) {
		// TODO: would it be nicer to get the symbol table via annotations?
		final Req2CauseTrackingPeaTransformer transformer = new Req2CauseTrackingPeaTransformer(mServices, mLogger);
		final Req2BoogieTranslator translator =
				new Req2BoogieTranslator(mServices, mLogger, patterns, Collections.singletonList(transformer));
		final ReqTestResultUtil mReporter =
				new ReqTestResultUtil(mLogger, mServices, translator.getReqSymbolTable(), transformer.getEffectStore());
		// register CEX transformer that removes program executions from CEX.
		final UnaryOperator<IResult> resultTransformer = mReporter::convertTraceAbstractionResult;
		mServices.getResultService().registerTransformer("CexReducer", resultTransformer);
		return translator.getUnit();
	}

	private IElement generateReqCheckRedundancyBoogie(final List<PatternType<?>> patterns) {
		final RedundancyTransformer transformer = new RedundancyTransformer(mServices, mLogger);
		final Req2BoogieTranslator translator =
				new Req2BoogieTranslator(mServices, mLogger, patterns, Collections.singletonList(transformer));
		final VerificationResultTransformer reporter =
				new VerificationResultTransformer(mLogger, mServices, translator.getReqSymbolTable());
		// register CEX transformer that removes program executions from CEX.
		final UnaryOperator<IResult> resultTransformer = reporter::convertTraceAbstractionResult;
		mServices.getResultService().registerTransformer("CexReducer", resultTransformer);
		return translator.getUnit();
	}

}
