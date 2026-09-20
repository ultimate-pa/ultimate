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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiExpansion;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.SingleThreadIcfg;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public final class ThreadAnalyzer {
	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final ConcurrentSymbolicTools mTools;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Collection<IcfgLocation> mRequestedLocationsOfInterest;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;
	private final List<String> mThreadIds;
	private final Set<String> mJoinedThreads;
	private final Map<String, IIcfg<IcfgLocation>> mThreadIcfgs = new HashMap<>();
	private final Map<String, Collection<IcfgLocation>> mThreadLois = new HashMap<>();
	private final Map<String, IcfgInterpreter> mThreadInterpreters = new HashMap<>();
	private final Map<String, Set<IcfgLocation>> mForkSourcesByThread;

	public ThreadAnalyzer(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final ConcurrentSymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> requestedLocationsOfInterest, final IDomain domain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final List<String> threadIds, final Set<String> joinedThreads) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mTools = tools;
		mIcfg = icfg;
		mRequestedLocationsOfInterest = Set.copyOf(requestedLocationsOfInterest);
		mDomain = domain;
		mFluid = fluid;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;
		mThreadIds = List.copyOf(threadIds);
		mJoinedThreads = Set.copyOf(joinedThreads);
		mForkSourcesByThread = collectForkSourcesByThread();
		prepareThreadIcfgsAndLois();
	}

	public Set<IcfgLocation> getJoinedExitLocations() {
		final Set<IcfgLocation> exits = new LinkedHashSet<>();
		for (final String threadId : mJoinedThreads) {
			final IcfgLocation exit = mThreadIcfgs.get(threadId).getProcedureExitNodes().get(threadId);
			if (exit != null) {
				exits.add(exit);
			}
		}
		return Set.copyOf(exits);
	}

	public void analyzeAllThreads(final IInterferenceSet interference, final ThreadInvariants threadInvariants) {
		threadInvariants.beginRound();
		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = mThreadIcfgs.get(threadId);

			mTools.configureForThread(threadId, interference, threadInvariants.locationInvariants(), mDomain);
			final IPredicate initialState = mTools.getInitialStatePredicate(threadId);

			final IcfgLocation entryLocation = threadIcfg.getProcedureEntryNodes().get(threadId);
			mTools.rememberThreadLocationState(entryLocation, initialState);
			final Map<IcfgLocation, IPredicate> threadResult = analyzeSingleThread(threadId, initialState);
			final Map<IcfgLocation, IPredicate> observed = mTools.getObservedThreadLocationStates();
			threadInvariants.updateThread(threadId, threadResult, observed);
		}
	}

	private Map<IcfgLocation, IPredicate> analyzeSingleThread(final String threadId, final IPredicate initialState) {
		final IcfgInterpreter interpreter = mThreadInterpreters.computeIfAbsent(threadId,
				this::createThreadInterpreter);
		return interpreter.interpret(initialState);
	}

	private void prepareThreadIcfgsAndLois() {
		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
			mThreadIcfgs.put(threadId, threadIcfg);
			final Collection<IcfgLocation> baseLois = LoiExpansion.getLocationsOfInterestForThread(threadId, threadIcfg,
					mRequestedLocationsOfInterest);
			final Set<IcfgLocation> expandedLois = new LinkedHashSet<>(baseLois);
			expandedLois.addAll(mForkSourcesByThread.getOrDefault(threadId, Set.of()));
			if (mJoinedThreads.contains(threadId)) {
				final IcfgLocation exit = threadIcfg.getProcedureExitNodes().get(threadId);
				if (exit != null) {
					expandedLois.add(exit);
				}
			}
			mThreadLois.put(threadId, List.copyOf(expandedLois));
		}
	}

	private IcfgInterpreter createThreadInterpreter(final String threadId) {
		final IIcfg<IcfgLocation> threadIcfg = mThreadIcfgs.get(threadId);
		final Collection<IcfgLocation> lois = mThreadLois.get(threadId);
		final IDomain effectiveDomain = mTools.getEffectiveDomain();
		final IDomain interpreterDomain = effectiveDomain != null ? effectiveDomain : mDomain;
		return new IcfgInterpreter(mLogger, mTimer, mStats, mTools, threadIcfg, lois, interpreterDomain, mFluid,
				mLoopSumFactory, mCallSumFactory);
	}

	private Map<String, Set<IcfgLocation>> collectForkSourcesByThread() {
		final Map<String, Set<IcfgLocation>> result = new LinkedHashMap<>();
		for (final var procedurePoints : mIcfg.getProgramPoints().values()) {
			for (final IcfgLocation location : procedurePoints.values()) {
				for (final var edge : location.getOutgoingEdges()) {
					if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
						result.computeIfAbsent(location.getProcedure(), ignored -> new LinkedHashSet<>()).add(location);
					}
				}
			}
		}
		return Map.copyOf(result);
	}
}
