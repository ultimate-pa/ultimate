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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.InterferenceCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiExpansion;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiMode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.SingleThreadIcfg;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.InterferenceCollector.ThreadAnalysisInput;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceOrchestrator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint.SubsumptionConvergenceCheck;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.transformers.IInterferenceTransformer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToPredicate;
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
    private final Set<String> mThreadIds;
    private final Collection<IcfgLocation> mLocationsOfInterest;
    private final IDomain mBaseDomain;
    private final IFluid mFluid;
    private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
    private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;
    private final LoiMode mLoiMode;

    // Interference components
    private final InterferenceOrchestrator mInterferenceAbstraction;
    private final LoiExpansion mLoiExpansion;

    public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
            final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
            final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
            final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
            final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
            final IUltimateServiceProvider services, final LoiMode loiMode) {
        mLogger = logger;
        mTimer = timer;
        mStats = stats;
        mTools = tools;
        mIcfg = icfg;
        mLocationsOfInterest = locationsOfInterest;
        mLoiMode = loiMode;
        mBaseDomain = baseDomain;
        mFluid = fluid;
        mLoopSumFactory = loopSumFactory;
        mCallSumFactory = callSumFactory;
        mLoiExpansion = new LoiExpansion(mLogger, mLocationsOfInterest, mIcfg, mLoiMode);

        // Initialize interference components - collect all thread IDs: main thread +
        // all forked procedures
        final Set<String> threadIds = new HashSet<>();
        threadIds.add(icfg.getInitialNodes().iterator().next().getProcedure());
        for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
            threadIds.add(fork.getNameOfForkedProcedure());
        }
        mThreadIds = threadIds;
        mLogger.info("Discovered threads for thread-modular analysis: " + mThreadIds);
        final PrimedDefaultIcfgSymbolTable primedSymbolTable = (PrimedDefaultIcfgSymbolTable) tools.getSymbolTable();
        final BasicPredicateFactory factory = tools.getFactory();

        final TransFormulaToPredicate translator = new TransFormulaToPredicate(services, tools.getManagedScript(),
                factory, primedSymbolTable);
        final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services,
                tools.getManagedScript(), factory, primedSymbolTable);

        // Create the shared interference abstraction with default pipeline components
        final InterferenceCollector collector = new InterferenceCollector(translator, true, tools.getManagedScript(),
                factory);
        mInterferenceAbstraction = new InterferenceOrchestrator(baseDomain, postcondition, collector,
                IInterferenceTransformer.identity(), IInterferenceMerger.identity(), mLogger);
    }

    @Override
    public Map<IcfgLocation, IPredicate> interpret() {

        final Map<IcfgLocation, IPredicate> result = new HashMap<>();
        InterferenceAbstraction previousInterferences = mInterferenceAbstraction.getInterferences();
        final SifaResultPrinter printer = new SifaResultPrinter(mLogger);
        int iteration = 0;

        // Outer fixpoint loop: iterate until interferences stabilize
        while (true) {
            iteration++;
            mLogger.info("=== Outer Fixpoint Iteration %d ===", iteration);
            // Store analysis results for all threads
            final Map<String, ThreadAnalysisInput> analysisResults = new HashMap<>();
            final Map<String, IIcfg<IcfgLocation>> threadIcfgs = new HashMap<>();

            // Analyze each thread
            for (final String threadId : mThreadIds) {
                mLogger.info(String.format("Analyzing thread: %s", threadId));
                // Create ConcurrentDomain for this thread with the shared abstraction
                // Pass the REAL fluid to ConcurrentDomain so it can decide when to apply base
                // abstraction
                final ConcurrentDomain concurrentDomain = new ConcurrentDomain(mBaseDomain, mInterferenceAbstraction,
                        threadId);

                final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
                threadIcfgs.put(threadId, threadIcfg);

                // Get LOIs for this thread.
                final Collection<IcfgLocation> threadLois = mLoiExpansion.getLocationsOfInterestForThread(threadId,
                        threadIcfg);

                // Create an interpreter with a "Force Abstraction" fluid.
                // This ensures the interpreter ALWAYS calls domain.alpha(), allowing
                // ConcurrentDomain
                // to apply interferences at every step.
                final IFluid forcingFluid = p -> true;

                final IcfgInterpreter interpreter = new IcfgInterpreter(mLogger, mTimer, mStats, mTools, threadIcfg,
                        threadLois, concurrentDomain, forcingFluid, mLoopSumFactory, mCallSumFactory);
                final Map<IcfgLocation, IPredicate> threadResult = interpreter.interpret();
                result.putAll(threadResult);

                // Store analysis result for interference collection
                analysisResults.put(threadId, new ThreadAnalysisInput(threadResult, threadIcfg));
            }

            // Update interferences via the abstraction (runs collect -> transform -> merge
            // pipeline)
            mInterferenceAbstraction.updateInterferences(analysisResults);
            final InterferenceAbstraction newInterferences = mInterferenceAbstraction.getInterferences();

            // Check fixpoint: are new interferences subsumed by old ones?
            if (SubsumptionConvergenceCheck.hasConverged(newInterferences, previousInterferences, mBaseDomain)) {
                mLogger.info("=== Fixpoint reached after %d iterations ===", iteration);
                break;
            }
            previousInterferences = newInterferences;
        }

        // Print final results
        // if (mLogger.isDebugEnabled()) {
        if (true) {
            printer.printResults(result);
        }

        // Filter the result to only include the locations of interest requested by the
        // caller.
        // We expanded the set of LOIs for the analysis to be sound (path-to-lois),
        // but we should only report results for the original set to avoid false
        // positives in the observer.
        result.keySet().retainAll(mLocationsOfInterest);
        return result;
    }

}
