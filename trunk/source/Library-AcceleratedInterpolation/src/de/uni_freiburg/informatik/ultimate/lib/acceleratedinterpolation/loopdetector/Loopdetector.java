/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop detector needed for
 *         {@link AcceleratedInterpolation}
 */
public class Loopdetector<LETTER extends IIcfgTransition<?>> implements ILoopdetector<LETTER> {

	private final List<LETTER> mTrace;
	private final List<IcfgLocation> mTraceLocations;
	private final ILogger mLogger;
	private Map<IcfgLocation, Set<List<LETTER>>> mLoops;
	private final Map<IcfgLocation, LETTER> mLoopExitTransitions;
	private final Map<IcfgLocation, Pair<Integer, Integer>> mLoopSize;
	private final Integer mDelay;
	private final IIcfg<? extends IcfgLocation> mIcfg;

	private final CycleFinder mCycleFinder;

	/**
	 * construct to find loops in a given trace.
	 *
	 * @param trace
	 * @param logger
	 * @param delay
	 *            How many iterations of a loop are needed until we decide to accelerate it. The lower the earlier the
	 *            loop gets accelerated.
	 */
	public Loopdetector(final List<LETTER> trace, final ILogger logger, final Integer delay,
			final IIcfg<? extends IcfgLocation> icfg) {
		mLogger = logger;
		mTrace = new ArrayList<>(trace);
		mCycleFinder = new CycleFinder();
		mIcfg = icfg;
		mTraceLocations = mCycleFinder.statementsToLocations(mTrace);
		mLoops = new HashMap<>();
		mLoopExitTransitions = new HashMap<>();
		mLoopSize = new HashMap<>();
		mDelay = delay;
		mLogger.debug("Loopdetector: created.");
		mLogger.debug("Loopdetector: Searching for Loops");
		findLoopPaths();
		if (!mLoops.isEmpty()) {
			checkDelay();
		}
	}

	/**
	 * Calculates loops from a given trace.
	 */
	private void findLoopPaths() {
		final Map<IcfgLocation, List<Integer>> possibleCycles = mCycleFinder.getCyclesInTrace(mTraceLocations);
		final Set<IcfgLocation> nestedCycles = getNestedCycles(possibleCycles);
		Map<IcfgLocation, List<Integer>> withoutNestedCycles = new HashMap<>(possibleCycles);
		for (final IcfgLocation nestedHead : nestedCycles) {
			withoutNestedCycles.remove(nestedHead);
		}
		withoutNestedCycles = filterProcedures(withoutNestedCycles);
		mLoops = cyclePaths(withoutNestedCycles);
		for (final Entry<IcfgLocation, List<Integer>> loop : withoutNestedCycles.entrySet()) {
			final IcfgLocation loopHead = loop.getKey();
			final List<Integer> loopSize = loop.getValue();
			final int loopExitTrans =
					withoutNestedCycles.get(loopHead).get(withoutNestedCycles.get(loopHead).size() - 1);
			mLoopExitTransitions.put(loopHead, mTrace.get(loopExitTrans));
			mLoopSize.put(loopHead, new Pair<>(loopSize.get(0), loopSize.get(loopSize.size() - 1)));
		}
		mLogger.debug("Found Loops");
	}

	/*
	 *
	 */
	private Map<IcfgLocation, List<Integer>> filterProcedures(final Map<IcfgLocation, List<Integer>> possibleCycles) {
		final Map<String, ? extends IcfgLocation> procEntries = mIcfg.getProcedureEntryNodes();
		final Map<IcfgLocation, List<Integer>> result = new HashMap<>();
		for (final Entry<IcfgLocation, List<Integer>> loop : possibleCycles.entrySet()) {
			final IcfgLocation loopHead = loop.getKey();
			final List<Integer> loopBody = new ArrayList<>(loop.getValue());
			final List<Integer> loopBodyNoProcedures = new ArrayList<>(loopBody);
			/*
			 * Allow only loops that either go through a procedure, meaning calling the procedure in another procedure.
			 * Or only loops inside a procedure. This prevents procedures themselves being recognized as loops
			 */
			for (int j = 0; j < loopBody.size() - 1; j++) {
				final Pair<Integer, Integer> currentLoop = new Pair<>(loopBody.get(j), loopBody.get(j + 1));
				for (int i = currentLoop.getFirst(); i <= currentLoop.getSecond(); i++) {
					final LETTER l = mTrace.get(i);
					/*
					 * Filter recursive programs.
					 */
					if (l instanceof ICallAction) {
						final Call call = (Call) l;
						if (call.getSucceedingProcedure().equals(call.getPrecedingProcedure())) {
							mLogger.debug("Found Recursive call!");
							loopBodyNoProcedures.remove(currentLoop.getSecond());
						}
					}
					if (l instanceof IReturnAction) {
						boolean foundCall = false;
						final Return ret = (Return) l;
						final Call call = ret.getCorrespondingCall();
						for (int k = i - 1; k > currentLoop.getFirst(); k--) {
							if (mTrace.get(k) == call) {
								foundCall = true;
							}
						}
						if (!foundCall) {
							loopBodyNoProcedures.remove(currentLoop.getSecond());
						}
					}
				}
			}
			if (loopBodyNoProcedures.size() > 1) {
				result.put(loopHead, loopBodyNoProcedures);
			}
		}
		return result;
	}

	/**
	 * Check if the loops are iterated through more than the delay states. If not, remove them, so that they do not get
	 * accelerated.
	 */
	private void checkDelay() {
		final Map<IcfgLocation, Set<List<LETTER>>> loopMap = new HashMap<>(mLoops);
		for (final Entry<IcfgLocation, Set<List<LETTER>>> loop : loopMap.entrySet()) {
			Integer smallestLoopSize = Integer.MAX_VALUE;
			for (final List<LETTER> loopsize : loop.getValue()) {
				if (loopsize.size() < smallestLoopSize) {
					smallestLoopSize = loopsize.size();
				}
			}
			final Pair<Integer, Integer> overallLoopSize = mLoopSize.get(loop.getKey());
			final Integer trueLoopSize = overallLoopSize.getSecond() - overallLoopSize.getFirst();
			final Integer delayCheck = smallestLoopSize * mDelay;
			if (delayCheck > trueLoopSize) {
				mLoops.remove(loop.getKey());
				mLoopSize.remove(loop.getKey());
				mLoopExitTransitions.remove(loop.getKey());
			}
		}
	}

	/**
	 * Transform an interval into statements of the trace.
	 *
	 * @param possibleCycles
	 * @return
	 */
	private Map<IcfgLocation, Set<List<LETTER>>> cyclePaths(final Map<IcfgLocation, List<Integer>> cycles) {
		final Map<IcfgLocation, Set<List<LETTER>>> cycleTransitions = new HashMap<>();
		for (final Entry<IcfgLocation, List<Integer>> cycle : cycles.entrySet()) {
			final Set<List<LETTER>> statements = new HashSet<>();
			final IcfgLocation loopHead = cycle.getKey();
			int i = 1;
			while (i < cycle.getValue().size()) {
				final List<LETTER> trace =
						new ArrayList<>(mTrace.subList(cycle.getValue().get(i - 1), cycle.getValue().get(i)));
				statements.add(trace);
				i++;
			}
			cycleTransitions.put(loopHead, statements);
		}
		return cycleTransitions;
	}

	/**
	 * Given a list of cycles with their respective repetition locations, check what kind of cycle each are: There are 2
	 * kind of cycles: 1: Disjunct -> They do not intersect, meaning there is a gap between the last repetition location
	 * of one cycle with the first repetition of the other 2: Nested -> Two loops are nested if the interval of
	 * repetitions of one loop lie within the interval of the other.
	 *
	 * We do not need nested loops.
	 *
	 * @param cyclesWithNested
	 *            List of cycles that are possibly nested
	 * @return
	 */
	private Set<IcfgLocation> getNestedCycles(final Map<IcfgLocation, List<Integer>> cyclesWithNested) {
		final Set<IcfgLocation> nestedCycles = new HashSet<>();
		for (final Iterator<Map.Entry<IcfgLocation, List<Integer>>> cycles =
				cyclesWithNested.entrySet().iterator(); cycles.hasNext();) {
			final Map.Entry<IcfgLocation, List<Integer>> cycle = cycles.next();
			final IcfgLocation loopHead = cycle.getKey();
			final int firstOccurence = cycle.getValue().get(0);
			final int lastOccurence = cycle.getValue().get(cycle.getValue().size() - 1);

			for (final Iterator<Map.Entry<IcfgLocation, List<Integer>>> otherCycles =
					cyclesWithNested.entrySet().iterator(); otherCycles.hasNext();) {
				final Map.Entry<IcfgLocation, List<Integer>> otherCycle = otherCycles.next();
				final IcfgLocation loopHeadOther = otherCycle.getKey();
				final int firstOccurenceOther = otherCycle.getValue().get(0);
				final int lastOccurenceOther = otherCycle.getValue().get(otherCycle.getValue().size() - 1);
				if (loopHead != loopHeadOther
						&& (firstOccurence < firstOccurenceOther && lastOccurence > lastOccurenceOther)
						|| firstOccurence < firstOccurenceOther && firstOccurenceOther < lastOccurence
								&& lastOccurenceOther > lastOccurence) {
					nestedCycles.add(loopHeadOther);
				}
			}
		}
		return nestedCycles;
	}

	@Override
	public Map<IcfgLocation, Set<List<LETTER>>> getLoops() {
		return mLoops;
	}

	public Map<IcfgLocation, LETTER> getLoopExitTransitions() {
		return mLoopExitTransitions;
	}

	public Map<IcfgLocation, Pair<Integer, Integer>> getLoopSize() {
		return mLoopSize;
	}

	public List<LETTER> getTrace() {
		return mTrace;
	}

	public List<IcfgLocation> getTraceLocations() {
		return mTraceLocations;
	}
}
