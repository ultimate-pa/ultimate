package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.DefaultInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.DefaultInterferenceAbstractor;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstractor;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public class ThreadModularSifaInterpreter implements ISifaInterpreter {

	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final SymbolicTools mTools;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IDomain mBaseDomain;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;

	private final Set<String> mThreadIds;
	private final IInterferenceAbstractor mAbstractor;
	private final RelationalPredicatePostcondition mPostcondition;
	private final LoiExpansion mLoiExpansion;
	private final ThreadModularProofChecker mProofChecker;
	private final SifaResultPrinter mResultPrinter;

	public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mTools = tools;
		mIcfg = icfg;
		mBaseDomain = baseDomain;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;

		mThreadIds = discoverThreadIds(icfg);
		mLoiExpansion = new LoiExpansion(logger);
		mResultPrinter = new SifaResultPrinter(logger);

		final var symbolTable = (PrimedDefaultIcfgSymbolTable) tools.getSymbolTable();
		final var factory = tools.getFactory();
		final var script = tools.getManagedScript();
		final var translator = new TransFormulaToInterferencePredicate(services, script, factory, symbolTable);
		mPostcondition = new RelationalPredicatePostcondition(services, script, factory, symbolTable);
		final var abstractor = new DefaultInterferenceAbstractor(translator, mPostcondition, baseDomain, true, script,
				factory, IInterferenceMerger.identity());
		// Debug logging (removable)
		abstractor.setLogger(logger);
		mAbstractor = abstractor;
		mProofChecker = new ThreadModularProofChecker(logger, icfg.getCfgSmtToolkit(), mPostcondition, baseDomain);
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		final FixpointResult fixpoint = computeInterferenceFixpoint();
		mResultPrinter.printResults(fixpoint.locationPredicates);
		verifyProof(fixpoint);
		return fixpoint.locationPredicates;
	}

	private static record IterationResult(Map<IcfgLocation, IPredicate> combinedPredicates,
			Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates,
			Map<String, IIcfg<IcfgLocation>> threadIcfgs) {
	}

	private static record FixpointResult(Map<IcfgLocation, IPredicate> locationPredicates,
			Map<String, Map<IcfgLocation, IPredicate>> threadPredicates, IInterferenceAbstraction interferences) {
	}

	private FixpointResult computeInterferenceFixpoint() {
		final Map<IcfgLocation, IPredicate> allPredicates = new HashMap<>();
		final DefaultInterferenceAbstraction emptyItf = DefaultInterferenceAbstraction.empty(mPostcondition);
		// Debug logging (removable)
		emptyItf.setLogger(mLogger);
		IInterferenceAbstraction interferences = emptyItf;
		for (int iteration = 1;; iteration++) {
			mLogger.info("=== Iteration %d ===", iteration);

			final IterationResult iterResult = analyzeAllThreads(interferences);
			allPredicates.putAll(iterResult.combinedPredicates);

			final IInterferenceAbstraction newInterferences = mAbstractor.abstractTransitionsToInterferenceAbstraction(
					iterResult.perThreadPredicates, iterResult.threadIcfgs);
			mResultPrinter.logInterferences(newInterferences);

			if (newInterferences.hasConverged(interferences, mBaseDomain)) {
				mLogger.info("=== Fixpoint reached after %d iterations ===", iteration);
				return new FixpointResult(allPredicates, iterResult.perThreadPredicates, newInterferences);
			}
			interferences = newInterferences;
		}
	}

	private IterationResult analyzeAllThreads(final IInterferenceAbstraction interferences) {
		final Map<IcfgLocation, IPredicate> combined = new HashMap<>();
		final Map<String, Map<IcfgLocation, IPredicate>> perThread = new HashMap<>();
		final Map<String, IIcfg<IcfgLocation>> icfgs = new HashMap<>();

		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
			icfgs.put(threadId, threadIcfg);

			final Map<IcfgLocation, IPredicate> threadResult = analyzeSingleThread(threadId, threadIcfg, interferences);
			combined.putAll(threadResult);
			perThread.put(threadId, threadResult);
		}

		return new IterationResult(combined, perThread, icfgs);
	}

	private Map<IcfgLocation, IPredicate> analyzeSingleThread(final String threadId,
			final IIcfg<IcfgLocation> threadIcfg, final IInterferenceAbstraction interferences) {
		final ConcurrentDomain domain = new ConcurrentDomain(mBaseDomain, interferences, threadId);
		final Collection<IcfgLocation> lois = mLoiExpansion.getLocationsOfInterestForThread(threadId, threadIcfg);
		final IFluid alwaysAbstract = p -> true;

		final IcfgInterpreter interpreter = new IcfgInterpreter(mLogger, mTimer, mStats, mTools, threadIcfg, lois,
				domain, alwaysAbstract, mLoopSumFactory, mCallSumFactory);
		return interpreter.interpret();
	}

	private void verifyProof(final FixpointResult fixpoint) {
		final var result = mProofChecker.checkAll(mIcfg, fixpoint.locationPredicates, fixpoint.interferences,
				fixpoint.threadPredicates);
		if (!result.isValid()) {
			mLogger.warn("Proof check failed: %d violations", result.getViolations().size());
		}
	}

	private Set<String> discoverThreadIds(final IIcfg<IcfgLocation> icfg) {
		final Set<String> ids = new HashSet<>();
		ids.add(icfg.getInitialNodes().iterator().next().getProcedure());
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			ids.add(fork.getNameOfForkedProcedure());
		}
		mLogger.info("Threads: %s", ids);
		return ids;
	}

}
