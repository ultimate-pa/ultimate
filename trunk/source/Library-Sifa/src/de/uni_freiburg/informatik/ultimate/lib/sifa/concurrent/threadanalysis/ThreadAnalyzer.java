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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiExpansion;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.SingleThreadIcfg;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.ThreadForkGraph;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public final class ThreadAnalyzer {
	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final ConcurrentSymbolicTools mConcurrentTools;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Collection<IcfgLocation> mRequestedLocationsOfInterest;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;
	private final Set<String> mJoinedThreads;
	private final Map<String, SingleThreadIcfg> mThreadIcfgs = new HashMap<>();
	private final Map<String, Collection<IcfgLocation>> mThreadLois = new HashMap<>();
	private final Map<String, IcfgInterpreter> mThreadInterpreters = new HashMap<>();
	private final ThreadForkGraph mForkGraph;

	public ThreadAnalyzer(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final ConcurrentSymbolicTools concurrentTools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> requestedLocationsOfInterest, final IDomain domain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final ThreadForkGraph forkGraph, final Set<String> joinedThreads) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mConcurrentTools = concurrentTools;
		mIcfg = icfg;
		mRequestedLocationsOfInterest = Set.copyOf(requestedLocationsOfInterest);
		mDomain = domain;
		mFluid = fluid;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;
		mForkGraph = forkGraph;
		mJoinedThreads = Set.copyOf(joinedThreads);
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
		for (final String threadId : mForkGraph.getThreadIds()) {
			final SingleThreadIcfg threadIcfg = mThreadIcfgs.get(threadId);

			mConcurrentTools.configureForThread(threadId, interference, threadInvariants.locationInvariants(), mDomain);
			try {
				final IcfgLocation entryLocation = threadIcfg.getProcedureEntryNodes().get(threadId);
				final IPredicate initialState = mConcurrentTools.applyInterferences(
						mConcurrentTools.getInitialStatePredicate(), entryLocation);

				mConcurrentTools.rememberThreadLocationState(entryLocation, initialState);
				final Map<IcfgLocation, IPredicate> threadResult = analyzeSingleThread(threadId, initialState);
				final Map<IcfgLocation, IPredicate> observed = mConcurrentTools.getObservedThreadLocationStates();
				threadInvariants.updateThread(threadId, threadResult, observed);
			} finally {
				mConcurrentTools.clearThreadContext();
			}
		}
	}

	private Map<IcfgLocation, IPredicate> analyzeSingleThread(final String threadId, final IPredicate initialState) {
		final IcfgInterpreter interpreter = mThreadInterpreters.computeIfAbsent(threadId,
				this::createThreadInterpreter);
		return interpreter.interpret(initialState);
	}

	private void prepareThreadIcfgsAndLois() {
		for (final String threadId : mForkGraph.getThreadIds()) {
			final SingleThreadIcfg threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
			mThreadIcfgs.put(threadId, threadIcfg);
			final Collection<IcfgLocation> baseLois = LoiExpansion.getLocationsOfInterestForThread(threadId, threadIcfg,
					mRequestedLocationsOfInterest);
			final Set<IcfgLocation> expandedLois = new LinkedHashSet<>(baseLois);
			expandedLois.addAll(mForkGraph.getForkSources(threadId));
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
		final SingleThreadIcfg threadIcfg = mThreadIcfgs.get(threadId);
		final Collection<IcfgLocation> lois = mThreadLois.get(threadId);
		return new IcfgInterpreter(mLogger, mTimer, mStats, mConcurrentTools, threadIcfg, lois, mDomain, mFluid,
				mLoopSumFactory, mCallSumFactory);
	}
}
