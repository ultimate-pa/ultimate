/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils;

import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Collects additional information about concurrent control flow graphs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <LOC>
 *            Type of locations in the CFG.
 */
public final class ExtendedConcurrencyInformation<LOC extends IcfgLocation> {
	private final IIcfg<LOC> mIcfg;

	private final HashRelation<IIcfgForkTransitionThreadCurrent<LOC>, IIcfgForkTransitionThreadOther<LOC>> mForks =
			new HashRelation<>();
	private final HashRelation<IIcfgJoinTransitionThreadCurrent<LOC>, IIcfgJoinTransitionThreadOther<LOC>> mJoins =
			new HashRelation<>();

	/**
	 * Create a new instance.
	 *
	 * @param icfg
	 *            The control flow graph for which concurrency information is collected. Procedure calls must be
	 *            inlined.
	 */
	public ExtendedConcurrencyInformation(final IIcfg<LOC> icfg) {
		mIcfg = icfg;

		for (final String thread : IcfgUtils.getAllThreadInstances(icfg)) {
			for (final IIcfgForkTransitionThreadOther<LOC> forkOther : getForksOf(thread)) {
				mForks.addPair(forkOther.getCorrespondingIIcfgForkTransitionCurrentThread(), forkOther);
			}
			for (final IIcfgJoinTransitionThreadOther<LOC> joinOther : getJoinsOf(thread)) {
				mJoins.addPair(joinOther.getCorrespondingIIcfgJoinTransitionCurrentThread(), joinOther);
			}
		}
	}

	public static boolean isThreadLocal(final IcfgEdge edge) {
		return !(edge instanceof IIcfgForkTransitionThreadOther<?>)
				&& !(edge instanceof IIcfgJoinTransitionThreadOther<?>);
	}

	/**
	 * Retrieve the fork transitions where a given thread is forked by another thread.
	 *
	 * @param forkedThread
	 *            The procedure name of a thread instance
	 * @return The set of all fork transitions where the given thread instance is forked by another thread
	 */
	public Set<IIcfgForkTransitionThreadOther<LOC>> getForksOf(final String forkedThread) {
		return mIcfg.getProcedureEntryNodes().get(forkedThread).getIncomingEdges().stream()
				.filter(IIcfgForkTransitionThreadOther.class::isInstance)
				.map(IIcfgForkTransitionThreadOther.class::cast).collect(Collectors.toSet());
	}

	/**
	 * Retrieve the join transitions where a given thread is joined by another thread.
	 *
	 * @param joinedThread
	 *            The procedure name of a thread instance
	 * @return The set of all join transitions where the given thread instance is joined into another thread
	 */
	public Set<IIcfgJoinTransitionThreadOther<LOC>> getJoinsOf(final String joinedThread) {
		return mIcfg.getProcedureExitNodes().get(joinedThread).getOutgoingEdges().stream()
				.map(IIcfgJoinTransitionThreadOther.class::cast).collect(Collectors.toSet());
	}

	public boolean mayBeForkOf(final String forkedThread, final IcfgEdge edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			return mForks.getImage((IIcfgForkTransitionThreadCurrent<LOC>) edge).stream()
					.anyMatch(e -> Objects.equals(e.getSucceedingProcedure(), forkedThread));
		}
		return false;
	}

	public boolean mayBeJoinOf(final String joinedThread, final IcfgEdge edge) {
		if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			return mJoins.getImage((IIcfgJoinTransitionThreadCurrent<LOC>) edge).stream()
					.anyMatch(e -> Objects.equals(e.getPrecedingProcedure(), joinedThread));
		}
		return false;
	}

	public boolean mustBeJoinOf(final String joinedThread, final IcfgEdge edge) {
		if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			return mJoins.getImage((IIcfgJoinTransitionThreadCurrent<LOC>) edge).stream()
					.allMatch(e -> Objects.equals(e.getPrecedingProcedure(), joinedThread));
		}
		return false;
	}
}
