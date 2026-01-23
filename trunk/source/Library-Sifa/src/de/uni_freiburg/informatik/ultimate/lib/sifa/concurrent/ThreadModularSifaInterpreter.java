package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
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
	private final Collection<IcfgLocation> mLocationsOfInterest;
	private final IDomain mBaseDomain;
	private final IFluid mFluid;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;

	public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mTools = tools;
		mIcfg = icfg;
		mLocationsOfInterest = locationsOfInterest;
		mBaseDomain = baseDomain;
		mFluid = fluid;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		// Thread entry procedures are exactly the initial nodes of the ICFG
		final Set<String> threadIds = mIcfg.getInitialNodes().stream()
				.map(IcfgLocation::getProcedure)
				.collect(Collectors.toSet());

		final Map<String, Set<IPredicate>> interferences = new HashMap<>();
		for (final String threadId : threadIds) {
			interferences.put(threadId, Collections.emptySet());
		}

		final Map<IcfgLocation, IPredicate> result = new HashMap<>();

		// Outer fixpoint loop: iterate until interferences stabilize
		// TODO: add actual fixpoint check (interferences unchanged)
		while (true) {
			for (final String threadId : threadIds) {
				final ConcurrentDomain concurrentDomain = new ConcurrentDomain(mBaseDomain, threadId, interferences);
				// Wrap ICFG to restrict initial nodes to this thread's entry point.
				// Pass all LOIs - CallGraph will filter to reachable ones automatically.
				final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
				final IcfgInterpreter interpreter = new IcfgInterpreter(mLogger, mTimer, mStats, mTools, threadIcfg,
						mLocationsOfInterest, concurrentDomain, mFluid, mLoopSumFactory, mCallSumFactory);
				final Map<IcfgLocation, IPredicate> threadResult = interpreter.interpret();
				result.putAll(threadResult);
			}

			// TODO: check if interferences changed, break if fixpoint reached
			break;
		}

		return result;
	}
}
