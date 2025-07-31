package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class AbstractLocationState<LOC extends IcfgLocation> {
	// global mapping of loc -> int, determined at beginning
	private final StaticAbstractLocationMap<LOC> mAbstractLocationMap;
	// state of other thread locs, changed by interferences
	private final AbstractLocationGlobalTracker mLocationTracker;
	private final int NOPREVIOUSLOCATION = -1;

	public AbstractLocationState(final LOC location, final StaticAbstractLocationMap<LOC> globalMap,
			final Set<String> threadNameSet) {
		mAbstractLocationMap = globalMap;
		final var tracker = new AbstractLocationGlobalTracker(threadNameSet, mAbstractLocationMap);
		final var abstractLocation = mAbstractLocationMap.getAbstractLocation(location);
		mLocationTracker = tracker.movedTo(location.getProcedure(), NOPREVIOUSLOCATION, abstractLocation);
	}

	public AbstractLocationState(final StaticAbstractLocationMap<LOC> locMap,
			final AbstractLocationGlobalTracker tracker) {
		mAbstractLocationMap = locMap;
		mLocationTracker = new AbstractLocationGlobalTracker(tracker);
	}

	public AbstractLocationGlobalTracker getTracker() {
		return mLocationTracker;
	}

	public StaticAbstractLocationMap<LOC> getLocationMap() {
		return mAbstractLocationMap;
	}

	public AbstractLocationState<LOC> union(final AbstractLocationState<LOC> other) {
		if (other == null || other.getTracker() == null) {
			return new AbstractLocationState<>(mAbstractLocationMap, mLocationTracker);
		}
		if (this.getTracker() == null) {
			return new AbstractLocationState<>(mAbstractLocationMap, other.getTracker());
		}
		return new AbstractLocationState<>(mAbstractLocationMap, mLocationTracker.union(other.getTracker()));
	}

	public AbstractLocationState<LOC> intersect(final AbstractLocationState<LOC> other) {
		final var trackIntersection = mLocationTracker.intersect(other.getTracker());
		if (trackIntersection == null) {
			return null;
		}
		return new AbstractLocationState<>(mAbstractLocationMap, trackIntersection);
	}

	public AbstractLocationState<LOC> intersectSelf(final AbstractLocationState<LOC> other) {
		final var trackIntersection = mLocationTracker.selfinterSect(other.getTracker());
		if (trackIntersection == null) {
			return null;
		}
		return new AbstractLocationState<>(mAbstractLocationMap, trackIntersection);
	}

	public AbstractLocationState<LOC> movedTo(final String threadName, final int locationOrigin,
			final int locationTarget) {
		return new AbstractLocationState<>(mAbstractLocationMap,
				mLocationTracker.movedTo(threadName, locationOrigin, locationTarget));
	}

	public AbstractLocationState<LOC> movedToInf(final String threadName, final int locationOrigin,
			final int locationTarget, final int abstractEntryLoc) {
		return new AbstractLocationState<>(mAbstractLocationMap,
				mLocationTracker.movedInf(threadName, locationOrigin, locationTarget, abstractEntryLoc));
	}

	public SubsetResult isSubsetOf(final AbstractLocationState<LOC> other) {
		final SubsetResult sr = mLocationTracker.isSubsetOf(other.mLocationTracker);
		return sr;
	}

	public boolean isEqualTo(final AbstractLocationState<LOC> other) {
		if (other == null) {
			return false;
		}
		return mLocationTracker.isEqualTo(other.mLocationTracker);
	}

	@Override
	public String toString() {
		final StringBuilder s = new StringBuilder();
		mLocationTracker.threadLocationMap().keySet()
				.forEach(k -> s.append(k + ":" + mLocationTracker.getLocationForThread(k).toString() + " "));
		return s.toString();
	}

	@Override
	public boolean equals(final Object o) {
		if (this == o) {
			return true;
		}
		if (!(o instanceof AbstractLocationState<?>)) {
			return false;
		}
		final AbstractLocationState<?> other = (AbstractLocationState<?>) o;
		return Objects.equals(mLocationTracker, other.mLocationTracker);
	}

	@Override
	public int hashCode() {
		return Objects.hashCode(mLocationTracker);
	}

}
