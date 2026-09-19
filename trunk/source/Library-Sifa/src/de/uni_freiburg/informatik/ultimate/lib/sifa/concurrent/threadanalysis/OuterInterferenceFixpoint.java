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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;

/**
 * Alternates thread analysis with interference and publication extraction until the outer fixpoint converges.
 */
public final class OuterInterferenceFixpoint {
	private static final int MAX_ITERATIONS = 100;
	private static final int MUTEX_INVARIANT_WIDENING_DELAY = 5;

	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final ConcurrentSymbolicTools mTools;
	private final IDomain mDomain;
	private final GroupedInterferenceFactory<?> mInterferenceFactory;
	private final PublishOnAcquire mInitialMutexInvariants;
	private final int mWideningThreshold;
	private final ThreadAnalysisRunner mThreadAnalysis;
	private final Set<IcfgLocation> mJoinedExitLocations;

	public OuterInterferenceFixpoint(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final ConcurrentSymbolicTools tools, final IDomain domain,
			final GroupedInterferenceFactory<?> interferenceFactory, final PublishOnAcquire initialMutexInvariants,
			final int wideningThreshold, final ThreadAnalysisRunner threadAnalysis) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mTools = tools;
		mDomain = domain;
		mInterferenceFactory = interferenceFactory;
		mInitialMutexInvariants = initialMutexInvariants;
		mWideningThreshold = wideningThreshold;
		mThreadAnalysis = threadAnalysis;
		mJoinedExitLocations = threadAnalysis.getJoinedExitLocations();
	}

	public ThreadModularFixpointResult compute() {
		final Map<IcfgLocation, IPredicate> allPredicates = new LinkedHashMap<>();
		IInterferenceSet currentInterferences = null;
		PublishOnAcquire currentMutexInvariants = mInitialMutexInvariants;
		boolean rerunWithStableInterferences = false;

		for (int iteration = 1;; iteration++) {
			checkProgress(iteration);
			mLogger.info("Iteration %d", iteration);
			final Map<IcfgLocation, IPredicate> joinedExitsBefore = mJoinedExitLocations.isEmpty() ? Map.of()
					: snapshotLocations(allPredicates, mJoinedExitLocations);
			mTools.setPublication(currentMutexInvariants);
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates = mThreadAnalysis.analyze(
					currentInterferences, allPredicates);
			final IInterferenceSet extractedInterferences = mInterferenceFactory.buildFromAllStates(perThreadPredicates);
			if (extractedInterferences != null) {
				mStats.add(Key.INTERFERENCE_SUMMARIES_BUILT, extractedInterferences.summaryCount());
			}
			final PublishOnAcquire extractedMutexInvariants = mInitialMutexInvariants.recomputePublishedInvariants(
					allPredicates, mDomain, mTools::postWithoutInterference);

			if (hasConverged(extractedInterferences, currentInterferences)
					&& extractedMutexInvariants.isSubsumedBy(currentMutexInvariants, mDomain)) {
				if (rerunWithStableInterferences || mJoinedExitLocations.isEmpty()
						|| joinedExitPredicatesUnchanged(allPredicates, joinedExitsBefore)) {
					return new ThreadModularFixpointResult(allPredicates, perThreadPredicates);
				}
				rerunWithStableInterferences = true;
				currentMutexInvariants = extractedMutexInvariants;
				continue;
			}

			rerunWithStableInterferences = false;
			currentMutexInvariants = iteration >= mWideningThreshold + MUTEX_INVARIANT_WIDENING_DELAY
					? currentMutexInvariants.widen(extractedMutexInvariants, mDomain)
					: extractedMutexInvariants;
			if (iteration >= mWideningThreshold) {
				currentInterferences = widen(currentInterferences, extractedInterferences);
				mStats.increment(Key.INTERFERENCE_OUTER_WIDENINGS);
			} else {
				currentInterferences = extractedInterferences;
			}
		}
	}

	private void checkProgress(final int iteration) {
		if (!mTimer.continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), "Timeout during outer thread-modular fixpoint");
		}
		if (iteration > MAX_ITERATIONS) {
			throw new ToolchainCanceledException(getClass(),
					"Outer thread-modular fixpoint did not converge after " + MAX_ITERATIONS + " iterations");
		}
	}

	private boolean hasConverged(final IInterferenceSet extracted, final IInterferenceSet current) {
		if (extracted == null) {
			return true;
		}
		if (current == null) {
			return false;
		}
		return extracted.isSubsumedBy(current, mDomain);
	}

	private IInterferenceSet widen(final IInterferenceSet current, final IInterferenceSet extracted) {
		return current == null ? extracted : current.widen(extracted, mDomain);
	}

	private static Map<IcfgLocation, IPredicate> snapshotLocations(final Map<IcfgLocation, IPredicate> allPredicates,
			final Set<IcfgLocation> locations) {
		final Map<IcfgLocation, IPredicate> snapshot = new LinkedHashMap<>(locations.size() * 2);
		for (final IcfgLocation location : locations) {
			snapshot.put(location, allPredicates.get(location));
		}
		return snapshot;
	}

	private boolean joinedExitPredicatesUnchanged(final Map<IcfgLocation, IPredicate> allPredicates,
			final Map<IcfgLocation, IPredicate> snapshot) {
		for (final var entry : snapshot.entrySet()) {
			final IPredicate before = entry.getValue();
			final IPredicate after = allPredicates.get(entry.getKey());
			if (before == after) {
				continue;
			}
			if (before == null || after == null) {
				return false;
			}
			if (!mDomain.isSubsetEq(before, after).isTrueForAbstraction()
					|| !mDomain.isSubsetEq(after, before).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}
}
