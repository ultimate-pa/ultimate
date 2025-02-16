package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class ThreadInstanceCounterFactory {
	private final CfgSmtToolkit mCfgSmtToolkit;

	public ThreadInstanceCounterFactory(final IIcfg<?> cfg) {
		mCfgSmtToolkit = cfg.getCfgSmtToolkit();
	}

	public ThreadInstanceCounter createBottomState() {
		final Map<String, Integer> bottomStateMap = new HashMap<>();
		final Set<String> threadNameSet = mCfgSmtToolkit.getProcedures();
		for (final String threadName : threadNameSet) {
			bottomStateMap.put(threadName, 0);
		}
		return new ThreadInstanceCounter(bottomStateMap);
	}

	public ThreadInstanceCounter createTopState() {
		final Map<String, Integer> topStateMap = new HashMap<>();
		final Set<String> threadNameSet = mCfgSmtToolkit.getProcedures();
		for (final String threadName : threadNameSet) {
			topStateMap.put(threadName, 2);
		}
		return new ThreadInstanceCounter(topStateMap);
	}

	public Set<String> computeForkingThreads(final String procedure) {
		final Set<String> forkingSet = new HashSet<>();
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : mCfgSmtToolkit.getConcurrencyInformation()
				.getThreadInstanceMap().keySet()) {
			if (fork.getNameOfForkedProcedure() == procedure) {
				forkingSet.add(fork.getSource().getProcedure());
			}
		}
		return forkingSet;
	}

	public ThreadInstanceCounter widen(final ThreadInstanceCounter first, final ThreadInstanceCounter second) {
		final Map<String, Integer> newThreadMap = new HashMap<>();
		final var firstMap = first.getThreadInstances();
		final var secondmap = second.getThreadInstances();
		for (final String threadName : first.getThreadNameSet()) {
			newThreadMap.put(threadName, Math.max(firstMap.get(threadName), secondmap.get(threadName)));
		}
		return new ThreadInstanceCounter(newThreadMap);
	}
}
