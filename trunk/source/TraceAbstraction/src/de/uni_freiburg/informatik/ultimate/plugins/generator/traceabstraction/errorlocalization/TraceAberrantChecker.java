package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization;

import java.io.Console;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.OverapproxVariable;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AberranceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAberrance;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;

/**
TODO
**/

public class TraceAberrantChecker<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final AberranceInformation[] mTraceAberrantList;
	private final IIcfgSymbolTable mSymbolTable;
	private final PredicateFactory mPredicateFactory;
	private final ErrorLocalizationStatisticsGenerator mErrorLocalizationStatisticsGenerator;

	// TODO ?
	private final boolean mApplyQuantifierElimination = true;
	
	
	public TraceAberrantChecker(final NestedRun<L, IPredicate> counterexample,
			final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IPredicateUnifier predicateUnifier,
			final RelevanceAnalysisMode faultLocalizationMode, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final IIcfg<IcfgLocation> IIcfg) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mSymbolTable = symbolTable;
		mPredicateFactory = predicateFactory;
		mTraceAberrantList = new AberranceInformation[counterexample.getWord().length()];
		for (int i = 0; i < mTraceAberrantList.length; i++) {
			mTraceAberrantList[i] = new AberranceInformation(TraceAberrance.MAYBE);
		}
		doTraceAberrantAnalysis(counterexample.getWord(), predicateUnifier.getTruePredicate(),
				predicateUnifier.getFalsePredicate(), modifiableGlobalsTable, csToolkit, predicateUnifier);
		
		mErrorLocalizationStatisticsGenerator = new ErrorLocalizationStatisticsGenerator();
		mErrorLocalizationStatisticsGenerator.continueErrorLocalizationTime();
		
	}
	
	public List<IRelevanceInformation> getAberranceInformation() {
		return Arrays.asList(mTraceAberrantList);
	}
	
	private void doTraceAberrantAnalysis(final NestedWord<L> counterexampleWord, final IPredicate truePredicate,
			final IPredicate falsePredicate, final ModifiableGlobalsTable modGlobVarManager,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier){
		// abort if no VariableOverapproximation in trace
		boolean abort = true;
		for (final IElement elem : counterexampleWord) {
			final Overapprox overapprox = OverapproxVariable.getAnnotation(elem);
			if (overapprox != null && overapprox instanceof OverapproxVariable) {
				abort = false;
				break;
			}
		}
		if (abort) {
			return;
		}
		
		// calculate Pre and Post
		final IterativePredicateTransformer<L> iptPre = new IterativePredicateTransformer<>(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				null, mPredicateFactory.not(falsePredicate), null, mPredicateFactory.not(falsePredicate), SimplificationTechnique.POLY_PAC,
				mXnfConversionTechnique, mSymbolTable);
		final IterativePredicateTransformer<L> iptSp = new IterativePredicateTransformer<>(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				truePredicate, null, null, mPredicateFactory.not(falsePredicate), SimplificationTechnique.POLY_PAC,
				mXnfConversionTechnique, mSymbolTable);
		final DefaultTransFormulas<L> dtf = new DefaultTransFormulas<>(counterexampleWord, truePredicate,
				falsePredicate, Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final List<IPredicatePostprocessor> postprocessors;
		if (false && mApplyQuantifierElimination) {
			final QuantifierEliminationPostprocessor qePostproc =
					new QuantifierEliminationPostprocessor(mServices, csToolkit.getManagedScript(), mPredicateFactory,
							SimplificationTechnique.POLY_PAC);
			postprocessors = Collections.singletonList(qePostproc);
		} else {
			postprocessors = Collections.emptyList();
		}
		TracePredicates preSequence;
		TracePredicates strongestPostconditionSequence;
		try {
			mLogger.info("started wp calc");
			preSequence = iptPre.computePreSequence(dtf, postprocessors, false);
			mLogger.info("started sp calc");
			strongestPostconditionSequence = iptSp.computeStrongestPostconditionSequence(dtf, postprocessors);
			mLogger.info("finished sp calc");
			// evtl nur teilweise
		} catch (TraceInterpolationException e) {
			throw new RuntimeException(e);
		}
		
		// 
		MonolithicHoareTripleChecker hc = new MonolithicHoareTripleChecker(csToolkit);
		FaultLocalizationRelevanceChecker faultLocalizationRelevanceChecker = new FaultLocalizationRelevanceChecker(mServices, csToolkit);
		List<IPredicate> preListDebug = new ArrayList<IPredicate>();
		for (int i = 0; i < counterexampleWord.length(); i++) {
			//ToolchainCanceledException
			Overapprox overapprox = OverapproxVariable.getAnnotation(counterexampleWord.getSymbol(i));
			if (null != overapprox && overapprox instanceof OverapproxVariable) {
				final IPredicate pre = preSequence.getPredicate(i+1);
				final IPredicate sp = strongestPostconditionSequence.getPredicate(i);
				preListDebug.add(pre);
				IInternalAction internal = faultLocalizationRelevanceChecker.constructHavocedInternalAction(mServices, (IInternalAction)counterexampleWord.getSymbol(i), csToolkit.getManagedScript());
				Validity res = (hc.checkInternal(sp, internal, pre));
				if (res == Validity.VALID) {
					mTraceAberrantList[i] = new AberranceInformation(TraceAberrance.NO);
				} else if (res == Validity.INVALID) {
					mTraceAberrantList[i] = new AberranceInformation(TraceAberrance.YES);
				} else {
					mTraceAberrantList[i] = new AberranceInformation(TraceAberrance.MAYBE);
				}
				//System.out.println("");
			}
		}
		//System.out.print("");
	}
}
