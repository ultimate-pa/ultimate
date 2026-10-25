/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.LockEdgeClassifier.Operation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.LockEdgeClassifier.Update;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * This analysis tracks which mutexes a thread holds at each location. We record a mutex as held only when the thread
 * holds it on every path to that location.
 *
 * A mutex can be stored in a global variable or in an array element such as {@code locks[0][1]}. We only track one
 * mutex per array. Every write to that array must lock or unlock the same element. If the program writes to other
 * elements, we do not track mutexes in that array. We also do not track a mutex if its array index can change while
 * other threads are running.
 */
public final class MustLocksetAnalysis {

	private record Mutex(IProgramVar variable, Set<TransFormula> acquires, Set<TransFormula> releases) {
	}

	private final Map<IcfgLocation, Set<IProgramVar>> mMustLocksetByLocation;
	private final Set<IProgramVar> mLockVars;

	private MustLocksetAnalysis(final Map<IcfgLocation, Set<IProgramVar>> mustLocksets,
			final Set<IProgramVar> lockVars) {
		mMustLocksetByLocation = Map.copyOf(mustLocksets);
		mLockVars = Set.copyOf(lockVars);
	}

	public static MustLocksetAnalysis disabled() {
		return new MustLocksetAnalysis(Map.of(), Set.of());
	}

	public static MustLocksetAnalysis create(final IIcfg<IcfgLocation> icfg, final ThreadActivityPreanalysis activity) {
		final Set<Mutex> mutexes = discoverMutexes(icfg, activity);
		if (mutexes.isEmpty()) {
			return disabled();
		}
		final Map<IcfgLocation, Set<IProgramVar>> heldLocksByLocation = computeHeldLocks(icfg, mutexes, activity);
		mutexes.removeIf(mutex -> hasReleaseWithoutHeldLock(mutex, icfg, heldLocksByLocation, activity));
		final Set<IProgramVar> lockVars = mutexes.stream().map(Mutex::variable).collect(Collectors.toSet());
		heldLocksByLocation
				.replaceAll((location, locks) -> Set.copyOf(DataStructureUtils.intersection(locks, lockVars)));
		return new MustLocksetAnalysis(heldLocksByLocation, lockVars);
	}

	public Set<IProgramVar> mustLocksetAt(final IcfgLocation location) {
		return location == null ? Set.of() : mMustLocksetByLocation.getOrDefault(location, Set.of());
	}

	/**
	 * This method returns the global variables that store the mutexes. For example, it returns {@code locks} for a
	 * mutex stored in {@code locks[0][1]}.
	 */
	public Set<IProgramVar> getLockVars() {
		return mLockVars;
	}

	private static Set<Mutex> discoverMutexes(final IIcfg<IcfgLocation> icfg,
			final ThreadActivityPreanalysis activity) {
		final List<? extends TransFormula> transitions =
				IcfgUtils.getAllLocations(icfg).flatMap(location -> location.getOutgoingEdges().stream())
						.map(IcfgEdge::getTransformula).filter(Objects::nonNull).distinct().toList();
		final Set<IProgramVar> stableIndexVars = stableIndexVars(icfg, activity);
		final ManagedScript script = icfg.getCfgSmtToolkit().getManagedScript();
		final Set<Mutex> mutexes = new LinkedHashSet<>();
		for (final IProgramVar variable : icfg.getCfgSmtToolkit().getSymbolTable().getGlobals()) {
			final Mutex mutex = recognizeMutex(variable, transitions, stableIndexVars, script);
			if (mutex != null) {
				mutexes.add(mutex);
			}
		}
		return mutexes;
	}

	private static Mutex recognizeMutex(final IProgramVar variable, final List<? extends TransFormula> transitions,
			final Set<IProgramVar> stableIndexVars, final ManagedScript script) {
		final Set<TransFormula> acquires = new LinkedHashSet<>();
		final Set<TransFormula> releases = new LinkedHashSet<>();
		List<Term> mutexIndices = null;
		for (final TransFormula transitionFormula : transitions) {
			if (!InterferenceUtils.getChangedGlobals(transitionFormula).contains(variable)) {
				continue;
			}
			final Update update = LockEdgeClassifier.classify(transitionFormula, variable, stableIndexVars, script);
			if (update == null || mutexIndices != null && !mutexIndices.equals(update.indices())) {
				return null;
			}
			mutexIndices = update.indices();
			if (update.operation() == Operation.ACQUIRE) {
				acquires.add(transitionFormula);
			} else {
				releases.add(transitionFormula);
			}
		}
		return acquires.isEmpty() ? null : new Mutex(variable, Set.copyOf(acquires), Set.copyOf(releases));
	}

	private static Set<IProgramVar> stableIndexVars(final IIcfg<IcfgLocation> icfg,
			final ThreadActivityPreanalysis activity) {
		final Set<IProgramVar> stableIndexVars =
				new LinkedHashSet<>(icfg.getCfgSmtToolkit().getSymbolTable().getGlobals());
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			if (!noOtherThreadsRunning(source, activity)) {
				for (final IcfgEdge edge : source.getOutgoingEdges()) {
					stableIndexVars.removeAll(InterferenceUtils.getChangedGlobals(edge.getTransformula()));
				}
			}
		});
		return stableIndexVars;
	}

	private static boolean hasReleaseWithoutHeldLock(final Mutex mutex, final IIcfg<IcfgLocation> icfg,
			final Map<IcfgLocation, Set<IProgramVar>> heldLocksByLocation, final ThreadActivityPreanalysis activity) {
		for (final IcfgLocation source : IcfgUtils.getAllLocations(icfg).toList()) {
			if (noOtherThreadsRunning(source, activity)
					|| heldLocksByLocation.getOrDefault(source, Set.of()).contains(mutex.variable())) {
				continue;
			}
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				if (edge.getTransformula() != null && mutex.releases().contains(edge.getTransformula())) {
					return true;
				}
			}
		}
		return false;
	}

	private static boolean noOtherThreadsRunning(final IcfgLocation location,
			final ThreadActivityPreanalysis activity) {
		return activity != null && !activity.hasOtherActiveThreadsAt(location);
	}

	private static Map<IcfgLocation, Set<IProgramVar>> computeHeldLocks(final IIcfg<IcfgLocation> icfg,
			final Set<Mutex> mutexes, final ThreadActivityPreanalysis activity) {
		final Map<IcfgLocation, Set<IProgramVar>> heldLocksByLocation = new LinkedHashMap<>();
		final Deque<IcfgLocation> worklist = new ArrayDeque<>();
		for (final IcfgLocation entry : icfg.getProcedureEntryNodes().values()) {
			heldLocksByLocation.put(entry, Set.of());
			worklist.add(entry);
		}
		while (!worklist.isEmpty()) {
			final IcfgLocation source = worklist.poll();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null) {
					continue;
				}
				// An index such as i in locks[i] may change while only this thread is running.
				// We clear the recorded locks because locks[i] could then refer to a mutex that this thread has not
				// locked.
				final Set<IProgramVar> locksAfterEdge = noOtherThreadsRunning(source, activity) ? Set.of()
						: updateHeldLocks(heldLocksByLocation.get(source), edge.getTransformula(), mutexes);
				if (mergeHeldLocksAt(target, locksAfterEdge, heldLocksByLocation)) {
					worklist.add(target);
				}
			}
		}
		return heldLocksByLocation;
	}

	private static boolean mergeHeldLocksAt(final IcfgLocation location, final Set<IProgramVar> incomingLocks,
			final Map<IcfgLocation, Set<IProgramVar>> heldLocksByLocation) {
		final Set<IProgramVar> previousLocks = heldLocksByLocation.get(location);
		final Set<IProgramVar> mergedLocks =
				previousLocks == null ? incomingLocks : DataStructureUtils.intersection(previousLocks, incomingLocks);
		if (mergedLocks.equals(previousLocks)) {
			return false;
		}
		heldLocksByLocation.put(location, Set.copyOf(mergedLocks));
		return true;
	}

	private static Set<IProgramVar> updateHeldLocks(final Set<IProgramVar> heldLocks,
			final TransFormula transitionFormula, final Set<Mutex> mutexes) {
		if (transitionFormula == null) {
			return heldLocks;
		}
		final Set<IProgramVar> result = new LinkedHashSet<>(heldLocks);
		for (final Mutex mutex : mutexes) {
			if (mutex.acquires().contains(transitionFormula)) {
				result.add(mutex.variable());
			} else if (mutex.releases().contains(transitionFormula)) {
				result.remove(mutex.variable());
			}
		}
		return result;
	}
}
