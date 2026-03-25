package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiExpansion;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.SingleThreadIcfg;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSetup;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

/**
 * Unsound baseline for performance comparison: analyze each thread once with empty interferences
 */
public class SinglePassConcurrentBaselineInterpreter implements ISifaInterpreter {
	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IDomain mAnalysisDomain;
	private final IFluid mFluid;
	private Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;
	private final Collection<IcfgLocation> mRequestedLocationsOfInterest;

	private final List<String> mThreadIds;
	private final LoiExpansion mLoiExpansion;
	private final SifaResultPrinter mResultPrinter;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ConcurrentSymbolicTools mConcurrentTools;

	public SinglePassConcurrentBaselineInterpreter(final ILogger logger, final IProgressAwareTimer timer,
			final SifaStats stats, final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mIcfg = icfg;
		mFluid = fluid;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;
		mRequestedLocationsOfInterest = locationsOfInterest == null ? Set.of() : Set.copyOf(locationsOfInterest);

		mLoiExpansion = new LoiExpansion();
		mConcurrentTools = (ConcurrentSymbolicTools) tools;
		final var setup = ThreadModularSetup.initialize(services, icfg, baseDomain, fluid, tools, mConcurrentTools,
				loopSumFactory);
		mThreadIds = setup.threadIds();
		mAnalysisDomain = setup.analysisDomain();
		mLoopSumFactory = setup.loopSumFactory();
		mPostcondition = setup.postcondition();
		mPostcondition.setStats(mStats);
		final var ghostVars = mConcurrentTools.getGhostVariables();
		final var absLocIds = ghostVars != null ? ghostVars.getAbstractLocationIds() : Map.<IcfgLocation, Integer>of();
		mResultPrinter = new SifaResultPrinter(logger, absLocIds, mConcurrentTools.getThreadActivityPreanalysis());
		mLogger.warn("Using unsound single-pass concurrent baseline (no interference fixpoint).");
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		final Map<IcfgLocation, IPredicate> combined = new HashMap<>();
		final InterferenceCollection interferences = InterferenceCollection.empty();
		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
			mConcurrentTools.configureForThread(threadId, interferences, combined, mAnalysisDomain, mAnalysisDomain,
					mPostcondition);
			final IPredicate initialState = mConcurrentTools.getInitialStatePredicate(threadId);
			final IcfgLocation entryLocation = threadIcfg.getProcedureEntryNodes().get(threadId);
			mConcurrentTools.rememberThreadLocationState(entryLocation, initialState);
			final Map<IcfgLocation, IPredicate> threadResult = analyzeSingleThread(threadId, threadIcfg, initialState);
			combined.putAll(mConcurrentTools.getObservedThreadLocationStates());
			combined.putAll(threadResult);
		}
		mResultPrinter.printResults(combined, mIcfg);
		return combined;
	}

	private Map<IcfgLocation, IPredicate> analyzeSingleThread(final String threadId,
			final IIcfg<IcfgLocation> threadIcfg, final IPredicate initialState) {
		final Collection<IcfgLocation> lois = mLoiExpansion.getLocationsOfInterestForThread(threadId, threadIcfg,
				mRequestedLocationsOfInterest);
		final IcfgInterpreter interpreter = new IcfgInterpreter(mLogger, mTimer, mStats, mConcurrentTools, threadIcfg,
				lois, mAnalysisDomain, mFluid, mLoopSumFactory, mCallSumFactory, initialState);
		return interpreter.interpret();
	}
}
