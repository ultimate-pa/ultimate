/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 *
 * Basic implementation of {@link IIcfg}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <LOC>
 *            The type of location.
 */
public class BasicIcfg<LOC extends IcfgLocation> extends BasePayloadContainer implements IIcfg<LOC> {

	private static final long serialVersionUID = 1L;
	private final Map<String, Map<DebugIdentifier, LOC>> mProgramPoints;
	private final Map<String, LOC> mEntryNodes;
	private final Map<String, LOC> mExitNodes;
	private final Map<String, Set<LOC>> mErrorNodes;
	private final Set<LOC> mLoopLocations;
	private CfgSmtToolkit mCfgSmtToolkit;
	private final Set<LOC> mInitialNodes;
	private final String mIdentifier;
	private final Class<LOC> mLocationClass;

	/**
	 * Create an empty {@link IIcfg}.
	 *
	 * @param identifier
	 *            A human-readable debug identifier.
	 * @param cfgSmtToolkit
	 *            A {@link CfgSmtToolkit} instance that has to contain all procedures and variables that may occur in
	 *            this {@link IIcfg}.
	 */
	public BasicIcfg(final String identifier, final CfgSmtToolkit cfgSmtToolkit, final Class<LOC> locClazz) {
		mLocationClass = Objects.requireNonNull(locClazz);
		mIdentifier = Objects.requireNonNull(identifier);
		mCfgSmtToolkit = Objects.requireNonNull(cfgSmtToolkit);

		mInitialNodes = new HashSet<>();
		mLoopLocations = new HashSet<>();
		mProgramPoints = new HashMap<>();
		mEntryNodes = new HashMap<>();
		mExitNodes = new HashMap<>();
		mErrorNodes = new HashMap<>();

		// initialize all maps with the known procedures
		for (final String proc : mCfgSmtToolkit.getProcedures()) {
			mProgramPoints.put(proc, new HashMap<>());
			mErrorNodes.put(proc, new HashSet<>());
		}
	}

	/**
	 * TODO: Documentation
	 */
	public void addProcedure(final String proc) {
		mProgramPoints.put(proc, new HashMap<>());
		mErrorNodes.put(proc, new HashSet<>());
	}

	/**
	 * Add a new location to this {@link IIcfg}. The location has to have a procedure that is already known by the
	 * {@link IIcfg}. Known procedures can be obtained from {@link CfgSmtToolkit#getProcedures()} via
	 * {@link #getCfgSmtToolkit()}.
	 *
	 * @param loc
	 *            The location that should be added.
	 * @param isInitial
	 *            true if it is an initial location.
	 * @param isError
	 *            true if it is an error location for its procedure.
	 * @param isProcEntry
	 *            true if it is the entry location for its procedure (it cannot overwrite existing procedure entry
	 *            locations).
	 * @param isProcExit
	 *            true if it is the exit location for its procedure (it cannot overwrite existing procedure exit
	 *            locations).
	 * @param isLoopLocation
	 *            true if it is a loop head.
	 */
	public void addLocation(final LOC loc, final boolean isInitial, final boolean isError, final boolean isProcEntry,
			final boolean isProcExit, final boolean isLoopLocation) {
		if (loc == null) {
			throw new IllegalArgumentException("Cannot add null location");
		}
		assert getLocationClass()
				.isAssignableFrom(loc.getClass()) : "Incompatible location types. Should be subclass of "
						+ getLocationClass() + " but is " + loc.getClass();
		final String proc = getProcedure(loc);
		final Map<DebugIdentifier, LOC> name2Loc = mProgramPoints.get(proc);
		assert name2Loc != null : "Unknown procedure";
		final LOC old = name2Loc.put(loc.getDebugIdentifier(), loc);
		if (loc.equals(old)) {
			// is already added
			return;
		}
		assert old == null : "Duplicate debug identifier for loc " + loc;

		if (isInitial) {
			mInitialNodes.add(loc);
		}
		if (isError) {
			final Set<LOC> procErrors = mErrorNodes.get(proc);
			assert procErrors != null : "Unknown procedure";
			procErrors.add(loc);
		}
		if (isProcEntry) {
			final LOC oldEntry = mEntryNodes.put(proc, loc);
			assert oldEntry == null || loc.equals(
					oldEntry) : "Do not overwrite the procedure entry node by mistake! Remove the old one first";
		}
		if (isProcExit) {
			final LOC oldExit = mExitNodes.put(proc, loc);
			assert oldExit == null || loc
					.equals(oldExit) : "Do not overwrite the procedure exit node by mistake! Remove the old one first";
		}
		if (isLoopLocation) {
			mLoopLocations.add(loc);
		}
	}

	/**
	 * Convenience method for {@link #addLocation(IcfgLocation, boolean, boolean, boolean, boolean, boolean)} without
	 * any true.
	 *
	 * TODO 2018-09-23 Matthias: I think methods like these are bad practice
	 * because the increase the overall complexity of the code
	 * <li> more methods == higher complexity of this class
	 * <li> method only used once
	 * <li> method introduces new terminology (what is an "ordinary" location)
	 * <li> if you use this method you have to read and understand the addLocation method anyway
	 *
	 * @param loc
	 *            The location to add.
	 */
	public void addOrdinaryLocation(final LOC loc) {
		addLocation(loc, false, false, false, false, false);
	}

	/**
	 * Remove the location <code>loc</code> from this {@link IIcfg} by removing it from all the maps. Note that this
	 * does not disconnect the location (i.e., loc itself remains unchanged)
	 *
	 * @param loc
	 *            The location to remove.
	 * @return True if the location was previously part of the IICfg, false otherwise.
	 */
	public boolean removeLocation(final IcfgLocation loc) {
		if (loc == null) {
			return false;
		}
		final String proc = getProcedure(loc);

		final Map<DebugIdentifier, LOC> name2loc = mProgramPoints.get(proc);
		if (name2loc == null) {
			return false;
		}
		final LOC removedLoc = name2loc.remove(loc.getDebugIdentifier());
		if (!loc.equals(removedLoc)) {
			assert removedLoc == null : "Multiple nodes with identical debug identifier!";
			return false;
		}

		final LOC entryLoc = mEntryNodes.get(proc);
		if (loc.equals(entryLoc)) {
			mEntryNodes.remove(proc);
		}

		final LOC exitLoc = mExitNodes.get(proc);
		if (loc.equals(exitLoc)) {
			mExitNodes.remove(proc);
		}

		final Set<LOC> errorLocs = mErrorNodes.get(proc);
		errorLocs.remove(loc);

		mLoopLocations.remove(loc);
		mInitialNodes.remove(loc);
		return true;
	}

	private static String getProcedure(final IcfgLocation loc) {
		final String proc = loc.getProcedure();
		assert proc != null : "Location " + loc + " does not have a procedure";
		return proc;
	}

	@Override
	public Map<String, Map<DebugIdentifier, LOC>> getProgramPoints() {
		return Collections.unmodifiableMap(mProgramPoints);
	}

	@Override
	public Map<String, LOC> getProcedureEntryNodes() {
		return Collections.unmodifiableMap(mEntryNodes);
	}

	@Override
	public Map<String, LOC> getProcedureExitNodes() {
		return Collections.unmodifiableMap(mExitNodes);
	}

	@Override
	public Map<String, Set<LOC>> getProcedureErrorNodes() {
		return Collections.unmodifiableMap(mErrorNodes);
	}

	@Override
	public Set<LOC> getLoopLocations() {
		return Collections.unmodifiableSet(mLoopLocations);
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mCfgSmtToolkit;
	}

	public void setCfgSmtToolkit(final CfgSmtToolkit cfgSmtToolkit) {
		mCfgSmtToolkit = cfgSmtToolkit;
	}

	@Override
	public Set<LOC> getInitialNodes() {
		return Collections.unmodifiableSet(mInitialNodes);
	}

	public Set<IcfgEdge> getInitialOutgoingEdges() {
		return getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toSet());
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	@Override
	public Class<LOC> getLocationClass() {
		return mLocationClass;
	}

	@Override
	public String toString() {
		return graphStructureToString();
	}
}
