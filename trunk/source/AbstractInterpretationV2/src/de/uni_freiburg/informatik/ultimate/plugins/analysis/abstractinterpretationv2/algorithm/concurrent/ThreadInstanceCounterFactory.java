package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class ThreadInstanceCounterFactory<LOC extends IcfgLocation> {
	private final Set<String> mThreadNameSet;

	public ThreadInstanceCounterFactory(final IIcfg<?> cfg) {
		mThreadNameSet = cfg.getCfgSmtToolkit().getProcedures();
	}

	public ThreadInstanceCounter<LOC> createBottomState() {
		final Map<String, Integer> bottomStateMap = new HashMap<>();
		for (final String threadName : mThreadNameSet) {
			bottomStateMap.put(threadName, 0);
		}
		return new ThreadInstanceCounter<>(bottomStateMap);
	}

	public ThreadInstanceCounter<LOC> createTopState() {
		final Map<String, Integer> topStateMap = new HashMap<>();
		for (final String threadName : mThreadNameSet) {
			topStateMap.put(threadName, 2);
		}
		return new ThreadInstanceCounter<>(topStateMap);
	}
}
