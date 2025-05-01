package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class AbstractLocationState<LOC extends IcfgLocation> {
	// global mapping of loc -> int, determined at beginning
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	// this states loc and abstract loc
	private final LOC mLocation;
	private final int mAbstractLocation;
	// state of other thread locs, changed by interferences
	private final AbstractLocationGlobalTracker mLocationTracker;

	public AbstractLocationState(final LOC location, final AbstractLocationMap<LOC> globalMap,
			final Set<String> threadNameSet) {
		mLocation = location;
		mAbstractLocationMap = globalMap;
		mAbstractLocation = mAbstractLocationMap.getAbstractLocation(location);
		final var tracker = new AbstractLocationGlobalTracker(threadNameSet, mAbstractLocationMap);
		mLocationTracker = tracker.movedTo(location.getProcedure(), mAbstractLocation);
	}

	public AbstractLocationState(final LOC location, final AbstractLocationMap<LOC> locMap,
			final AbstractLocationGlobalTracker tracker) {
		mLocation = location;
		mAbstractLocationMap = locMap;
		mAbstractLocation = mAbstractLocationMap.getAbstractLocation(location);
		final var track = new AbstractLocationGlobalTracker(tracker);
		mLocationTracker = track.movedTo(location.getProcedure(), mAbstractLocation);
	}

	public AbstractLocationState(final AbstractLocationState<LOC> other) {
		mLocation = other.mLocation;
		mAbstractLocationMap = other.mAbstractLocationMap;
		mAbstractLocation = other.mAbstractLocation;
		final var track = new AbstractLocationGlobalTracker(other.mLocationTracker);
		mLocationTracker = track.movedTo(mLocation.getProcedure(), mAbstractLocation);
	}

	public AbstractLocationState(final LOC loc, final AbstractLocationState<LOC> other) {
		mLocation = loc;
		mAbstractLocationMap = other.mAbstractLocationMap;
		mAbstractLocation = other.mAbstractLocation;
		final var track = new AbstractLocationGlobalTracker(other.mLocationTracker);
		mLocationTracker = track.movedTo(mLocation.getProcedure(), mAbstractLocation);
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

	public LOC getLoc() {
		return mLocation;
	}

	public int getintLoc() {
		return mAbstractLocation;
	}

	public AbstractLocationState<LOC> union(final AbstractLocationState<LOC> other) {
		if (other == null || other.getTracker() == null) {
			return new AbstractLocationState<>(mLocation, mAbstractLocationMap, mLocationTracker);
		}
//		if (mLocation != other.mLocation) {
//			throw new AssertionError(
//					"You are trying to merge states of different locations. Move the location of one to the correct one.");
//		}
		return new AbstractLocationState<>(mLocation, mAbstractLocationMap, mLocationTracker.union(other.getTracker()));
	}

	public AbstractLocationState<LOC> intersect(final AbstractLocationState<LOC> other) {
		return new AbstractLocationState<>(mLocation, mAbstractLocationMap,
				mLocationTracker.intersect(other.getTracker()));
	}

	public AbstractLocationState<LOC> movedTo(final String threadName, final int newLocation) {
		if (threadName == mLocation.getProcedure()) {
			if (mLocation.getOutgoingNodes().size() == 0) {
				return new AbstractLocationState<>(mLocation, mAbstractLocationMap,
						mLocationTracker.movedTo(threadName, newLocation));
			}
			return new AbstractLocationState<>((LOC) mLocation.getOutgoingNodes().getFirst(), mAbstractLocationMap,
					mLocationTracker.movedTo(threadName, newLocation));

		}
		return new AbstractLocationState<>(mLocation, mAbstractLocationMap,
				mLocationTracker.movedTo(threadName, newLocation));

	}

	public SubsetResult isSubsetOf(final AbstractLocationState<LOC> other) {
		final SubsetResult sr = mLocationTracker.isSubsetOf(other.mLocationTracker);
		return sr;
	}

	public boolean isEqualTo(final AbstractLocationState<LOC> other) {
		if (other == null) {
			return false;
		}
		if (other.mAbstractLocation != mAbstractLocation) {
			return false;
		}
		return mLocationTracker.isEqualTo(other.mLocationTracker);
	}

	public String printLocation() {
		return String.valueOf(mAbstractLocation);
	}

	@Override
	public String toString() {
		final StringBuilder s = new StringBuilder();
		mLocationTracker.threadLocationMap().keySet()
				.forEach(k -> s.append(k + ":" + mLocationTracker.getLocationForThread(k).toString() + " "));
		s.append(" My location: " + mAbstractLocation);
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
		if (!Objects.equals(mLocation, other.mLocation)) {
			return false;
		}
		if (mAbstractLocation != other.mAbstractLocation) {
			return false;
		}
		return Objects.equals(mLocationTracker, other.mLocationTracker);
	}

	@Override
	public int hashCode() {
		int result = Objects.hashCode(mLocation);
		result = result + Integer.hashCode(mAbstractLocation);
		result = result + Objects.hashCode(mLocationTracker);
		return result;
	}

}
