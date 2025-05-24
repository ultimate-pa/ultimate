package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class AbstractLocationState<LOC extends IcfgLocation> {
	// global mapping of loc -> int, determined at beginning
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	// state of other thread locs, changed by interferences
	private final AbstractLocationGlobalTracker mLocationTracker;

	public AbstractLocationState(final LOC location, final AbstractLocationMap<LOC> globalMap,
			final Set<String> threadNameSet) {
		mAbstractLocationMap = globalMap;
		final var tracker = new AbstractLocationGlobalTracker(threadNameSet, mAbstractLocationMap);
		final var abstractLocation = mAbstractLocationMap.getAbstractLocation(location);
		mLocationTracker = tracker.movedTo(location.getProcedure(), abstractLocation);
	}

	public AbstractLocationState(final AbstractLocationMap<LOC> locMap, final AbstractLocationGlobalTracker tracker) {
		mAbstractLocationMap = locMap;
		mLocationTracker = new AbstractLocationGlobalTracker(tracker);
	}

	public AbstractLocationState(final LOC location, final AbstractLocationMap<LOC> locMap,
			final AbstractLocationGlobalTracker tracker) {
		mAbstractLocationMap = locMap;
		final var track = new AbstractLocationGlobalTracker(tracker);
		final var abstractLocation = mAbstractLocationMap.getAbstractLocation(location);
		mLocationTracker = track.movedTo(location.getProcedure(), abstractLocation);
	}

	public AbstractLocationState(final LOC location, final AbstractLocationState<LOC> other) {
		mAbstractLocationMap = other.mAbstractLocationMap;
		final var track = new AbstractLocationGlobalTracker(other.mLocationTracker);
		final var abstractLocation = mAbstractLocationMap.getAbstractLocation(location);
		mLocationTracker = track.movedTo(location.getProcedure(), abstractLocation);
	}

	public AbstractLocationState<LOC> copyToNewState(final LOC newLoc) {
		return new AbstractLocationState<>(newLoc, mAbstractLocationMap, mLocationTracker);
	}

	public AbstractLocationGlobalTracker getTracker() {
		return mLocationTracker;
	}

	public AbstractLocationMap<LOC> getLocationMap() {
		return mAbstractLocationMap;
	}

	public boolean equalThreadTracking(final AbstractLocationState<LOC> other) {
		return mLocationTracker.isEqualTo(other.mLocationTracker);
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

	public AbstractLocationState<LOC> movedTo(final String threadName, final int newLocationInt) {
		return new AbstractLocationState<>(mAbstractLocationMap, mLocationTracker.movedTo(threadName, newLocationInt));
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

	public String printLocation(final String sourcethread) {
		return String.valueOf(mLocationTracker.getLocationForThread(sourcethread));
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
