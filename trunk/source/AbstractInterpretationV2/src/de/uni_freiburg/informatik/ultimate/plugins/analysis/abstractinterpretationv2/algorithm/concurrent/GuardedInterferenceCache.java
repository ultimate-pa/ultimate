package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

record StateItfPrestatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
		STATE state, STATE itfPrestate, ACTION itf) {
}

record StateItfPair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
		STATE state, ACTION itf) {
}

record IntersectionPair<STATE extends IAbstractState<STATE>>(STATE state1, STATE state2) {
}

public class GuardedInterferenceCache<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final Map<StateItfPair<STATE, ACTION, LOC>, Collection<STATE>> postOpCache = new LRUCache<>(10000);
	private final Map<StateItfPrestatePair<STATE, ACTION, LOC>, Collection<STATE>> itfCache = new LRUCache<>(10000);
	private final Map<IntersectionPair<STATE>, STATE> intersectionCache = new LRUCache<>(10000);

	public GuardedInterferenceCache() {
	}

	public Map<StateItfPair<STATE, ACTION, LOC>, Collection<STATE>> getPostOpCache() {
		return postOpCache;
	}

	public Map<StateItfPrestatePair<STATE, ACTION, LOC>, Collection<STATE>> getItfCache() {
		return itfCache;
	}

	public Map<IntersectionPair<STATE>, STATE> getIntersectionCache() {
		return intersectionCache;
	}

	private class LRUCache<K, V> extends LinkedHashMap<K, V> {
		private static final long serialVersionUID = 1L;
		private final int maxEntries;

		public LRUCache(final int maxEntries) {
			super(maxEntries + 1, 0.75f, true);
			this.maxEntries = maxEntries;
		}

		@Override
		protected boolean removeEldestEntry(final Map.Entry<K, V> eldest) {
			return size() > maxEntries;
		}
	}
}
