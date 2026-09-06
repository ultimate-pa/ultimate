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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class InitialStateFactory {

	private static final String MAIN_THREAD = "ULTIMATE.start";

	private final ConcurrentSymbolicTools mTools;
	private final IIcfg<IcfgLocation> mIcfg;

	private GhostVariableManager mGhostVariables;
	private Map<IcfgLocation, IPredicate> mLocationPredicates;
	private IDomain mAnalysisDomain;

	public InitialStateFactory(final ConcurrentSymbolicTools tools, final IIcfg<IcfgLocation> icfg) {
		mTools = Objects.requireNonNull(tools);
		mIcfg = Objects.requireNonNull(icfg);
	}

	public void configureStaticAnalysis(final GhostVariableManager ghostVariables) {
		mGhostVariables = ghostVariables;
	}

	public void configureForThread(final Map<IcfgLocation, IPredicate> locationPredicates,
			final IDomain analysisDomain) {
		mLocationPredicates = Objects.requireNonNull(locationPredicates);
		mAnalysisDomain = Objects.requireNonNull(analysisDomain);
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		final IcfgLocation entryLocation = mIcfg.getProcedureEntryNodes().get(threadId);

		if (threadId.equals(MAIN_THREAD)) {
			final IPredicate mainState = getMainThreadInitialState();
			return mTools.applyInterferences(mainState, entryLocation);
		}

		final Set<IPredicate> forkStates = collectForkStates(threadId);
		if (forkStates.isEmpty()) {
			return mTools.bottom();
		}
		IPredicate result = null;
		for (final IPredicate pred : forkStates) {
			result = result == null ? pred : mAnalysisDomain.join(result, pred);
		}
		return mTools.applyInterferences(result, entryLocation);
	}

	private IPredicate getMainThreadInitialState() {
		if (mGhostVariables == null) {
			return mTools.top();
		}
		return mTools.predicate(mGhostVariables.createInitialLocationState(MAIN_THREAD));
	}

	/*
	 * For a non-main thread, start from every place where some other thread can fork it and join those states.
	 */
	private Set<IPredicate> collectForkStates(final String threadId) {
		final Set<IPredicate> states = new LinkedHashSet<>();
		final ConcurrencyInformation concInfo = mIcfg.getCfgSmtToolkit().getConcurrencyInformation();
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : concInfo.getThreadInstanceMap().keySet()) {
			if (!fork.getNameOfForkedProcedure().equals(threadId)) {
				continue;
			}
			final IPredicate forkState = mLocationPredicates.get(fork.getSource());
			if (forkState == null) {
				continue;
			}
			states.add(applyForkEffects(forkState, fork));
		}
		return states;
	}

	/*
	 * The new thread should start right after the fork. We cannot just use the post-state at the fork target, because
	 * that may already contain interferences (even from itself). So we use the fork source state and only apply the
	 * fork-local location updates.
	 */
	private IPredicate applyForkEffects(final IPredicate forkState,
			final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork) {
		final IPredicate sharedForkState = projectToSharedState(forkState);
		if (mGhostVariables == null) {
			return sharedForkState;
		}
		final String forkedThreadId = fork.getNameOfForkedProcedure();
		final String forkingTid = fork.getSource().getProcedure();
		final IcfgLocation forkedEntry = mGhostVariables.getEntryLocation(forkedThreadId);

		final IPredicate updated = mTools.addLocationUpdateForThread(sharedForkState, forkingTid, fork.getTarget());
		return mTools.addLocationUpdateForThread(updated, forkedThreadId, forkedEntry);
	}

	private IPredicate projectToSharedState(final IPredicate predicate) {
		return InterferenceUtils.projectToGlobalState(predicate, mTools.getServices(), mTools.getManagedScript(),
				mTools::predicate);
	}
}
