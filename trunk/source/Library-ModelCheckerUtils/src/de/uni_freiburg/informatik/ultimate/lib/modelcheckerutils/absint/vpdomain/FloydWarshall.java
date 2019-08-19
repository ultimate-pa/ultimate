/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Implementation of the Floyd-Warshall algorithm. Takes an undirected weighted graph as input, together with an
 * ordering of the edge weights and a "plus" operation for the edge weights.
 *
 * Returns (via getResult) a version of the graph where the triangle inequality holds (edge weights have been lowered
 * if necessary).
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <VERTEX>
 * @param <EDGELABEL>
 */
class FloydWarshall<VERTEX, EDGELABEL> {

	private final BiPredicate<EDGELABEL, EDGELABEL> mSmallerThan;

	private BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> mPlus;
//	private TriFunction<EDGELABEL, EDGELABEL, VERTEX, EDGELABEL> mOtherPlus;

	private BiFunction<Pair<EDGELABEL, EDGELABEL>, Triple<VERTEX, VERTEX, VERTEX>, EDGELABEL> mOtherPlus;


	private final EDGELABEL mNullLabel;

	private final Map<Doubleton<VERTEX>, EDGELABEL> mDist;
	private final List<VERTEX> mVertices;
	private boolean mPerformedChanges;
	private final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> mMeet;

	public FloydWarshall(final BiPredicate<EDGELABEL, EDGELABEL> smallerThan,
			final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> plus,
			final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> meet,
			final EDGELABEL nullLabel,
			final Map<Doubleton<VERTEX>, EDGELABEL> graph,
			final Function<EDGELABEL, EDGELABEL> labelCloner) {
		this(smallerThan, meet, nullLabel, graph, labelCloner);
		mPlus = Objects.requireNonNull(plus);
		run();
	}

	/**
	 *
	 * @param smallerThan
	 * @param plus
	 * @param meet
	 * @param nullLabel
	 * @param graph
	 * @param labelCloner
	 * @param useOtherPlus just so the erasures are not equal
	 */
	public FloydWarshall(final BiPredicate<EDGELABEL, EDGELABEL> smallerThan,
//			final TriFunction<EDGELABEL, EDGELABEL, VERTEX, EDGELABEL> plus,
			final BiFunction<
				Pair<EDGELABEL, EDGELABEL>,
				Triple<VERTEX, VERTEX, VERTEX>,
				EDGELABEL> plus,
			final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> meet,
			final EDGELABEL nullLabel,
			final Map<Doubleton<VERTEX>, EDGELABEL> graph,
			final Function<EDGELABEL, EDGELABEL> labelCloner,
			final boolean useOtherPlus) {
		this(smallerThan, meet, nullLabel, graph, labelCloner);
		mOtherPlus = Objects.requireNonNull(plus);
		run();
	}


	/**
	 *
	 *
	 * @param smallerThan partial order operator (non-strict)
	 * @param plus
	 * @param nullLabel
	 * @param graph
	 * @param labelCloner
	 */
	private FloydWarshall(final BiPredicate<EDGELABEL, EDGELABEL> smallerThan,
//			final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> plus,
			final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> meet,
			final EDGELABEL nullLabel,
			final Map<Doubleton<VERTEX>, EDGELABEL> graph,
			final Function<EDGELABEL, EDGELABEL> labelCloner) {
		mSmallerThan = smallerThan;
//		mPlus = plus;
		mMeet = meet;
		mNullLabel = nullLabel;
		mPerformedChanges = false;

		// initialize with a deep copy of the input graph

		// TODO: dreiecksmatrix statt map
		mDist = new HashMap<>();

		final HashSet<VERTEX> verticeSet = new HashSet<>();
		for (final Entry<Doubleton<VERTEX>, EDGELABEL> en : graph.entrySet()) {
			verticeSet.add(en.getKey().getOneElement());
			verticeSet.add(en.getKey().getOtherElement());
			mDist.put(en.getKey(), labelCloner.apply(en.getValue()));
		}
		mVertices = new ArrayList<>(verticeSet);

	}

	public boolean performedChanges() {
		return mPerformedChanges;
	}

	/**
	 * execute the main loop of the Floyd-Warshall algorithm
	 */
	private void run() {
		for (int k = 0; k < mVertices.size(); k++) {
			for (int i = 0; i < mVertices.size(); i++) {
				if (i == k) {
					continue;
				}
				for (int j = 0; j < mVertices.size(); j++) {
					if (j == i || j == k || i > j) {
						continue;
					}
					final EDGELABEL distIj = getDist(i, j);
					final EDGELABEL distIk = getDist(i, k);
					final EDGELABEL distKj = getDist(k, j);
					assert (mPlus == null) != (mOtherPlus == null);
					final EDGELABEL ikPlusKj = mPlus != null ?
							mPlus.apply(distIk, distKj) :
								mOtherPlus.apply(new Pair<>(distIk, distKj),
										new Triple<>(mVertices.get(i), mVertices.get(k), mVertices.get(j)));

					if (!mSmallerThan.test(distIj, ikPlusKj)) {
						final EDGELABEL ikPlusKjMeetIj = mMeet.apply(ikPlusKj, distIj);
						mDist.put(new Doubleton<>(mVertices.get(i), mVertices.get(j)), ikPlusKjMeetIj);
						mPerformedChanges = true;
					}
				}
			}
		}
	}

	private EDGELABEL getDist(final int i, final int j) {
		EDGELABEL res = mDist.get(new Doubleton<>(mVertices.get(i), mVertices.get(j)));
		if (res == null) {
			res = mNullLabel;
		}
		return res;
	}

	public Map<Doubleton<VERTEX>, EDGELABEL> getResult() {
		return Collections.unmodifiableMap(mDist);
	}
}