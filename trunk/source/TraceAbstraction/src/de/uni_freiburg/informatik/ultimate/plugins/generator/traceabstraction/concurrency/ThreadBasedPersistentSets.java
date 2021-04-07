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

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class ThreadBasedPersistentSets implements IPersistentSetChoice<IcfgEdge, IPredicate> {
	private final ILogger mLogger;
	private final IIcfg<?> mIcfg;
	private final IIndependenceRelation<?, IcfgEdge> mIndependence;

	private int mQueries;
	private int mTrivialQueries;
	private long mComputationTime;

	public ThreadBasedPersistentSets(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final IIndependenceRelation<?, IcfgEdge> independence) {
		assert independence.isSymmetric() : "Not ready for semi-commutativity";
		assert !independence.isConditional() : "Not ready for conditional independence";

		mLogger = services.getLoggingService().getLogger(ThreadBasedPersistentSets.class);
		mIcfg = icfg;
		mIndependence = independence;
	}

	@Override
	public Set<IcfgEdge> persistentSet(final IPredicate state) {
		final IMLPredicate mlState = (IMLPredicate) state;
		if (mlState.getProgramPoints().length <= 1) {
			return null;
		}

		if (mQueries % 20_000 == 0) {
			mLogger.warn("Computed %d persistent sets (%.2f %% trivial) in %d s", mQueries,
					(100.0 * mTrivialQueries) / mQueries, mComputationTime / 1000);
		}
		mQueries++;

		final long start = System.currentTimeMillis();
		for (final IcfgLocation loc : mlState.getProgramPoints()) {
			final String thread = loc.getProcedure();
			if (loc.getOutgoingEdges().isEmpty()) {
				continue;
			}
			if (hasLaterJoins(thread, loc)) {
				continue;
			}

			final boolean allCommute = mIcfg.getCfgSmtToolkit().getProcedures().stream()
					.allMatch(other -> other.equals(thread) || commuteAll(loc, other));
			if (allCommute) {
				mComputationTime += System.currentTimeMillis() - start;
				return new HashSet<>(loc.getOutgoingEdges());
			}
		}

		mTrivialQueries++;
		mComputationTime += System.currentTimeMillis() - start;
		return null;
	}

	private boolean hasLaterJoins(final String thread, final IcfgLocation currentLoc) {
		return getThreadActions(thread)
				.anyMatch(action -> isJoin(action) && !currentLoc.getOutgoingEdges().contains(action));
	}

	private static boolean isJoin(final IcfgEdge action) {
		return action instanceof IIcfgJoinTransitionThreadCurrent<?>
				|| action instanceof IIcfgJoinTransitionThreadOther<?>;
	}

	private boolean commuteAll(final IcfgLocation loc, final String thread) {
		for (final IcfgEdge other : getThreadActions(thread).collect(Collectors.toSet())) {
			for (final IcfgEdge action : loc.getOutgoingEdges()) {
				if (!mIndependence.contains(null, action, other)) {
					return false;
				}
			}
		}
		return true;
	}

	private Stream<IcfgEdge> getThreadActions(final String thread) {
		return mIcfg.getProgramPoints().get(thread).values().stream().flatMap(loc -> loc.getOutgoingEdges().stream());
	}
}
