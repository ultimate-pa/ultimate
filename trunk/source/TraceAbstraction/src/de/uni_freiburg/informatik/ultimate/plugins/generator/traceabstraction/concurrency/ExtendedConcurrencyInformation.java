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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ReverseIcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

/**
 * Collects additional information about concurrent control flow graphs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ExtendedConcurrencyInformation {
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final Map<String, Set<IIcfgJoinTransitionThreadOther<IcfgLocation>>> mThreadJoins = new HashMap<>();
	private final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, IIcfgJoinTransitionThreadOther<IcfgLocation>> mCorrespondingJoins =
			new HashMap<>();

	private final HashRelation<String, String> mComputedReachableJoins = new HashRelation<>();
	private final HashRelation3<IcfgLocation, String, IIcfgJoinTransitionThreadOther<IcfgLocation>> mReachableJoins =
			new HashRelation3<>();

	/**
	 * Create a new instance.
	 *
	 * @param icfg
	 *            The control flow graph for which concurrency information is collected. Procedure calls must be
	 *            inlined.
	 */
	public ExtendedConcurrencyInformation(final IIcfg<?> icfg) {
		mIcfg = icfg;
	}

	private static boolean isThreadLocal(final IcfgEdge edge) {
		return !(edge instanceof IIcfgForkTransitionThreadOther<?>)
				&& !(edge instanceof IIcfgJoinTransitionThreadOther<?>);
	}

	/**
	 * The inverse of {@link IIcfgJoinTransitionThreadOther::getCorrespondingIIcfgJoinTransitionCurrentThread}.
	 *
	 * @param join
	 *            A join transition whose twin IIcfgJoinTransitionThreadOther shall be retrieved
	 * @return the corresponding IIcfgJoinTransitionThreadOther instance
	 */
	public IIcfgJoinTransitionThreadOther<IcfgLocation>
			getJoinOther(final IIcfgJoinTransitionThreadCurrent<IcfgLocation> join) {
		final IIcfgJoinTransitionThreadOther<IcfgLocation> other = mCorrespondingJoins.get(join);
		if (other != null) {
			return other;
		}

		for (final String thread : mIcfg.getCfgSmtToolkit().getProcedures()) {
			getJoinsOf(thread);
			final IIcfgJoinTransitionThreadOther<IcfgLocation> otherJoin = mCorrespondingJoins.get(join);
			if (otherJoin != null) {
				return otherJoin;
			}
		}

		throw new IllegalArgumentException();
	}

	/**
	 * Retrieve the join transitions where a given thread is joined by another thread.
	 *
	 * @param joinedThread
	 *            The procedure name of a thread instance
	 * @return The set of all join transitions where the given thread instance is joined into another thread
	 */
	public Set<IIcfgJoinTransitionThreadOther<IcfgLocation>> getJoinsOf(final String joinedThread) {
		final Set<IIcfgJoinTransitionThreadOther<IcfgLocation>> cachedJoins = mThreadJoins.get(joinedThread);
		if (cachedJoins != null) {
			return cachedJoins;
		}

		final Set<IIcfgJoinTransitionThreadOther<IcfgLocation>> joins = new HashSet<>();
		final var iterator = new IcfgEdgeIterator(mIcfg.getProcedureEntryNodes().get(joinedThread),
				ExtendedConcurrencyInformation::isThreadLocal);
		while (iterator.hasNext()) {
			final IcfgEdge edge = iterator.next();
			if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
				final var join = (IIcfgJoinTransitionThreadOther<IcfgLocation>) edge;
				joins.add(join);
				assert !mCorrespondingJoins.containsKey(join.getCorrespondingIIcfgJoinTransitionCurrentThread())
						|| mCorrespondingJoins.get(
								join.getCorrespondingIIcfgJoinTransitionCurrentThread()) == join : "duplicated join";
				mCorrespondingJoins.put(join.getCorrespondingIIcfgJoinTransitionCurrentThread(), join);
			}
		}
		mThreadJoins.put(joinedThread, Collections.unmodifiableSet(joins));
		return joins;
	}

	/**
	 * Retrieves all joins of a given thread that can be reached from a given source location (within its thread).
	 *
	 * @param source
	 *            the source location from which a join (in the same thread) must be reachable
	 * @param joinedThread
	 *            the thread being joined
	 * @return all join transitions satisfying the above criteria
	 */
	public Set<IIcfgJoinTransitionThreadOther<IcfgLocation>> getReachableJoinsOf(final IcfgLocation source,
			final String joinedThread) {
		if (!mComputedReachableJoins.containsPair(source.getProcedure(), joinedThread)) {
			computeReachableJoins(source.getProcedure(), joinedThread);
		}
		return mReachableJoins.projectToTrd(source, joinedThread);
	}

	private void computeReachableJoins(final String joiningThread, final String joinedThread) {
		for (final var joinOther : getJoinsOf(joinedThread)) {
			final var joinCurrent = joinOther.getCorrespondingIIcfgJoinTransitionCurrentThread();
			if (!joinCurrent.getPrecedingProcedure().equals(joiningThread)) {
				continue;
			}

			final var iterator =
					new ReverseIcfgEdgeIterator(Collections.singleton((IcfgJoinThreadCurrentTransition) joinCurrent),
							ExtendedConcurrencyInformation::isThreadLocal);
			while (iterator.hasNext()) {
				final IcfgEdge edge = iterator.next();
				mReachableJoins.addTriple(edge.getSource(), joinedThread, joinOther);
			}
		}
		mComputedReachableJoins.addPair(joiningThread, joinedThread);
	}
}
