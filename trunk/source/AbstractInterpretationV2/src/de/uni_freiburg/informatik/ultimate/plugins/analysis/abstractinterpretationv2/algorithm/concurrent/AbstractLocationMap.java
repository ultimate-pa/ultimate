package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

public final class AbstractLocationMap<LOC> {
	private final Map<LOC, Integer> mMap = new ConcurrentHashMap<>();
	private final Function<LOC, Integer> mMappingFunction;
	private final Map<String, ? extends LOC> mEntryLocs;

	public AbstractLocationMap(final Function<LOC, Integer> mappingFunction,
			final Map<String, ? extends LOC> entryLocs) {
		mMappingFunction = mappingFunction;
		mEntryLocs = entryLocs;
	}

	public int getAbstractEntryLoc(final String threadName) {
		return getAbstractLocation(mEntryLocs.get(threadName));
	}

	public LOC getEntryLoc(final String threadName) {
		return mEntryLocs.get(threadName);
	}

	public int getAbstractLocation(final LOC loc) {
		return mMap.computeIfAbsent(loc, mMappingFunction);
	}
}
