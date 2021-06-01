/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.DominatorComputation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public final class IcfgDominatorInfo<LOC extends IcfgLocation> {
	// The value null represents the artificial "root edge".
	private static final IcfgEdge ROOT_EDGE = null;

	private final IIcfg<LOC> mIcfg;
	private final Map<IcfgEdge, Set<IcfgEdge>> mEdgeDomination;
	private final HashRelation<IcfgEdge, IcfgEdge> mRealEdgeMap;

	public IcfgDominatorInfo(final IIcfg<LOC> icfg) {
		mIcfg = icfg;
		mRealEdgeMap = getForkJoinMap(icfg);
		mEdgeDomination = computeEdgeDominators();
	}

	private static <LOC extends IcfgLocation> HashRelation<IcfgEdge, IcfgEdge> getForkJoinMap(final IIcfg<LOC> icfg) {
		final HashRelation<IcfgEdge, IcfgEdge> result = new HashRelation<>();
		final Iterator<IcfgEdge> it = new IcfgEdgeIterator(icfg);
		while (it.hasNext()) {
			final IcfgEdge edge = it.next();
			if (edge instanceof IIcfgForkTransitionThreadOther<?>) {
				final IIcfgForkTransitionThreadOther<LOC> fork = (IIcfgForkTransitionThreadOther<LOC>) edge;
				result.addPair((IcfgEdge) fork.getCorrespondingIIcfgForkTransitionCurrentThread(), edge);
			}
			if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
				final IIcfgJoinTransitionThreadOther<LOC> join = (IIcfgJoinTransitionThreadOther<LOC>) edge;
				result.addPair((IcfgEdge) join.getCorrespondingIIcfgJoinTransitionCurrentThread(), edge);
			}
		}
		return result;
	}

	private Stream<IcfgEdge> getRealEdges(final IcfgEdge edge) {
		if (mRealEdgeMap.hasEmptyImage(edge)) {
			return Stream.of(edge);
		}
		return mRealEdgeMap.getImage(edge).stream();
	}

	private Stream<IcfgEdge> realIncoming(final IcfgLocation loc) {
		return loc.getIncomingEdges().stream().flatMap(this::getRealEdges);
	}

	private Stream<IcfgEdge> realOutgoing(final IcfgLocation loc) {
		return loc.getOutgoingEdges().stream().flatMap(this::getRealEdges);
	}

	private Map<IcfgEdge, Set<IcfgEdge>> computeEdgeDominators() {
		final Set<IcfgEdge> allEdges = Stream.concat(new IcfgEdgeIterator(mIcfg).asStream(), Stream.of(ROOT_EDGE))
				.flatMap(this::getRealEdges).collect(Collectors.toSet());
		return new DominatorComputation<>(allEdges, ROOT_EDGE, e -> getPredecessorEdges(e, allEdges)).getResult();
	}

	// We pass the set of all reachable edges. This is needed e.g. to rule out fork transitions from non-instantiated
	// thread templates.
	private Set<IcfgEdge> getPredecessorEdges(final IcfgEdge edge, final Set<IcfgEdge> reachableEdges) {
		if (edge == ROOT_EDGE) {
			return Collections.emptySet();
		}

		final Set<IcfgEdge> pred = realIncoming(edge.getSource()).filter(reachableEdges::contains)
				.collect(Collectors.toCollection(HashSet::new));
		if (mIcfg.getInitialNodes().contains(edge.getSource())) {
			pred.add(ROOT_EDGE);
		}
		if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
			final IcfgLocation loc = ((IIcfgJoinTransitionThreadOther<?>) edge)
					.getCorrespondingIIcfgJoinTransitionCurrentThread().getSource();
			pred.addAll(realIncoming(loc).filter(reachableEdges::contains).collect(Collectors.toSet()));
		}
		return pred;
	}

	public boolean isDominatedBy(final IcfgEdge edge1, final IcfgEdge edge2) {
		Objects.requireNonNull(edge1);
		Objects.requireNonNull(edge2);
		return mEdgeDomination.get(edge1).contains(edge2);
	}

	public boolean isDominatedBy(final IcfgEdge edge, final LOC loc) {
		Objects.requireNonNull(edge);
		Objects.requireNonNull(loc);
		return realOutgoing(loc).anyMatch(out -> isDominatedBy(edge, out));
	}

	public boolean isDominatedBy(final LOC loc, final IcfgEdge edge) {
		Objects.requireNonNull(loc);
		Objects.requireNonNull(edge);
		if (mIcfg.getInitialNodes().contains(loc)) {
			return false;
		}
		return realIncoming(loc).allMatch(in -> isDominatedBy(in, edge));
	}

	public boolean isDominatedBy(final LOC loc1, final LOC loc2) {
		Objects.requireNonNull(loc1);
		Objects.requireNonNull(loc2);
		if (mIcfg.getInitialNodes().contains(loc2)) {
			return Objects.equals(loc1, loc2);
		}
		if (Objects.equals(loc1, loc2)) {
			return true;
		}
		return realIncoming(loc1).allMatch(in -> isDominatedBy(in, loc2));
	}
}