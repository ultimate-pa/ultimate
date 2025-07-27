package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;

public class ThreadInstanceCounterFactory<LOC extends IcfgLocation> {
	private final Set<String> mThreadNameSet;

	public ThreadInstanceCounterFactory(final IIcfg<?> cfg) {
		mThreadNameSet = cfg.getCfgSmtToolkit().getProcedures();
	}

	public ThreadInstanceCounter<LOC> createBottomState() {
		final Map<String, IntervalDomainValue> bottomStateMap = new HashMap<>();
		final IntervalDomainValue zero = new IntervalDomainValue(0, 0);
		for (final String threadName : mThreadNameSet) {
			bottomStateMap.put(threadName, zero);
		}
		return new ThreadInstanceCounter<>(bottomStateMap);
	}

	public ThreadInstanceCounter<LOC> createTopState() {
		final Map<String, IntervalDomainValue> topStateMap = new HashMap<>();
		for (final String threadName : mThreadNameSet) {
			topStateMap.put(threadName, new IntervalDomainValue());
		}
		return new ThreadInstanceCounter<>(topStateMap);
	}
}
