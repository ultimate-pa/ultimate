/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Preference order representing the transitive closure of the Union of two preference Orders, used to define products
 * of monitors.
 *
 * @param <L>
 *            The type of the transition letters.
 * @param <S0>
 *            The state type of the program.
 * @param <S1>
 *            The state type of mLeftAutomaton.
 * @param <S2>
 *            The state type of mRightAutomaton.
 * @param <S>
 *            The state type of the combination.
 */
public class ProductPreferenceOrder<L, S0, S1, S2, S> implements IPreferenceOrder<L, S0, S> {
	private final IPreferenceOrder<L, S0, S1> mFirstOrder;
	private final IPreferenceOrder<L, S0, S2> mSecondOrder;
	private final IProductPreferenceOrderStateFactory<S1, S2, S> mStateFactory;
	private final ProductPreferenceOrderAutomaton<L, S1, S2, S> mAutomaton;

	private final Map<Pair<S0, S>, ProductComparator<L>> mCachedComparators = new HashMap<>();

	public ProductPreferenceOrder(final IPreferenceOrder<L, S0, S1> fst, final IPreferenceOrder<L, S0, S2> snd,
			final IProductPreferenceOrderStateFactory<S1, S2, S> stateFactory) {
		mFirstOrder = fst;
		mSecondOrder = snd;
		mStateFactory = stateFactory;
		mAutomaton = new ProductPreferenceOrderAutomaton<>(mFirstOrder.getMonitor(), mSecondOrder.getMonitor(),
				mStateFactory);
	}

	public static <L, S> IPreferenceOrder<L, S, ?> create(final IPreferenceOrder<L, S, ?> fst,
			final IPreferenceOrder<L, S, ?> snd) {
		return new ProductPreferenceOrder<>(fst, snd, new IProductPreferenceOrderStateFactory.Default<>());
	}

	@Override
	public boolean isPositional() {
		return mFirstOrder.isPositional() || mSecondOrder.isPositional();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, S> getMonitor() {
		return mAutomaton;
	}

	@Override
	public Comparator<L> getOrder(final S0 programState, final S monitorState) {
		final Pair<S0, S> key =
				isPositional() ? new Pair<>(programState, monitorState) : new Pair<>(null, monitorState);
		return mCachedComparators.computeIfAbsent(key, k -> createOrder(k.getFirst(), k.getSecond()));
	}

	private ProductComparator<L> createOrder(final S0 programState, final S monitorState) {
		return new ProductComparator<>(mFirstOrder.getOrder(programState, mStateFactory.getLeftState(monitorState)),
				mSecondOrder.getOrder(programState, mStateFactory.getRightState(monitorState)),
				mAutomaton.getAlphabet()); // this might need to be something more complicated
	}

	public interface IProductPreferenceOrderStateFactory<S1, S2, S> extends IStateFactory<S> {
		S createProductState(S1 leftState, S2 rightState);

		S1 getLeftState(S state);

		S2 getRightState(S state);

		class Default<S1, S2> implements IProductPreferenceOrderStateFactory<S1, S2, Pair<S1, S2>> {
			@Override
			public Pair<S1, S2> createProductState(final S1 leftState, final S2 rightState) {
				return new Pair<>(leftState, rightState);
			}

			@Override
			public S1 getLeftState(final Pair<S1, S2> state) {
				return state.getFirst();
			}

			@Override
			public S2 getRightState(final Pair<S1, S2> state) {
				return state.getSecond();
			}
		}
	}

	/** Represents the transitive closure of the union of two given orders lessX and lessY. */
	private static class ProductComparator<L> implements Comparator<L> {
		private final Map<Pair<L, L>, Integer> mComparisonResults = new HashMap<>();

		public ProductComparator(final Comparator<L> lessX, final Comparator<L> lessY, final Set<L> alphabet) {
			// Maybe refactor this to throw exceptions if contradictions arise?
			// First create the union of the orders
			for (final L l1 : alphabet) {
				for (final L l2 : alphabet) {
					final int resultX = lessX.compare(l1, l2);
					final int resultY = lessY.compare(l1, l2);
					if (resultX != 0) {
						mComparisonResults.put(new Pair<>(l1, l2), resultX);
					} else {
						// Either resultY != 0 or resultX = resultY = 0
						mComparisonResults.put(new Pair<>(l1, l2), resultY);
					}
				}
			}

			// Then apply the Floyd-Warshall algorithm to get the transitive closure
			for (final L k : alphabet) {
				for (final L i : alphabet) {
					for (final L j : alphabet) {
						final int result_ij = mComparisonResults.get(new Pair<>(i, j));
						final int result_ik = mComparisonResults.get(new Pair<>(i, k));
						final int result_kj = mComparisonResults.get(new Pair<>(k, j));
						// If we i and j are already comparable, then we don't care
						if (result_ij == 0) {
							// i < k < j -> i < j
							if (result_ik == 1 && result_kj == 1) {
								mComparisonResults.put(new Pair<>(i, j), -1);
							}
							// i > k > j -> i > j
							else if (result_ik == -1 && result_kj == -1) {
								mComparisonResults.put(new Pair<>(i, j), 1);
							}
						}

					}
				}
			}
		}

		@Override
		public int compare(final L o1, final L o2) {
			return mComparisonResults.get(new Pair<>(o1, o2));
		}
	}
}
