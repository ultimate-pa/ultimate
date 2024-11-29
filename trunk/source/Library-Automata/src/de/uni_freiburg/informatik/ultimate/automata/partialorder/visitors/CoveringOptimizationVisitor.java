/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * A visitor that implements an optimization based on a covering relation between different states of the explored
 * automaton: When encountering a transition, such that another state was previously discovered which covers the
 * transition's target state, exploration of the transition successor is stopped.
 *
 * Possible applications in verification and POR include:
 * <ul>
 * <li>Prune states if a previously explored state has the same program location but a weaker predicate (interpolant),
 * similar to covering e.g. in Impact</li>
 * <li>In sleep set reduction, prune a state if the same automaton state was previously explored with a smaller sleep
 * set</li>
 * </ul>
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the explored automaton
 * @param <S>
 *            The type of states in the explored automaton
 */
public class CoveringOptimizationVisitor<L, S> extends WrapperVisitor<L, S, IDfsVisitor<L, S>> {
	private final IGeneralizedCoveringRelation<S> mCoveringRelation;
	private final CoveringMode mMode;
	private final Map<Object, Set<S>> mCoveringMap = new HashMap<>();

	/**
	 * Describes the behaviour when a transition is discovered whose target is covered by an already-explored state:
	 * Either the exploration of the target is simply pruned (but the current transition is kept as-is), or the current
	 * transition is redirected to the covering state (however, re-exploration of the covering state is stopped).
	 *
	 * The former behaviour (PRUNE) is more suited for emptiness checks, the latter (REDIRECT) is e.g. also suitable for
	 * automaton-constructing visitors.
	 */
	public enum CoveringMode {
		PRUNE, REDIRECT
	}

	/**
	 * Creates a new visitor.
	 *
	 * @param underlying
	 *            An underlying visitor to which calls are proxied.
	 * @param coveringRelation
	 *            A covering relation used for optimization.
	 * @param mode
	 *            The covering mode used in the optimization
	 */
	public CoveringOptimizationVisitor(final IDfsVisitor<L, S> underlying, final ICoveringRelation<S> coveringRelation,
			final CoveringMode mode) {
		super(underlying);
		mCoveringRelation = coveringRelation;
		mMode = mode;
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		final Set<S> cover = getCoveringStates(target);
		switch (mMode) {
		case REDIRECT:
			if (cover == null) {
				return super.discoverTransition(source, letter, target);
			}
			for (final var old : cover) {
				super.discoverTransition(source, letter, old);
			}
			return true;
		case PRUNE:
			if (cover != null) {
				return true;
			}
			return super.discoverTransition(source, letter, target);
		default:
			throw new UnsupportedOperationException("Unsupported covering mode: " + mMode);
		}
	}

	private Set<S> getCoveringStates(final S state) {
		final Object key = mCoveringRelation.getKey(state);
		final Set<S> cover = mCoveringMap.get(key);
		if (cover == null || cover.contains(state)) {
			return null;
		}

		return mCoveringRelation.coveringStates(cover, state);
	}

	@Override
	public boolean discoverState(final S state) {
		final Object key = mCoveringRelation.getKey(state);
		mCoveringMap.computeIfAbsent(key, x -> new HashSet<>()).add(state);
		return super.discoverState(state);
	}

	/**
	 * A covering relation between states of an automaton.
	 *
	 * The meaning of covering in an automaton is this: If state <code>q</code> covers state <code>p</code>, then the
	 * language of all words accepted from <code>q</code> must be a superset of the states accepted from <code>p</code>.
	 * (The reverse implication need not hold.)
	 *
	 * As such, a trivial covering relation is given by <code>Objects::equals</code>. However, depending on the
	 * particular automaton, larger and thus more useful covering relations can often be computed.
	 *
	 * Covering relations must be reflexive: It is always sound to add the reflexive pairs to the covering relation
	 * (without violating the above implication), it should be reasonably efficient to call <code>Objects::equal</code>,
	 * and some derived covering relation constructions rely on their input relations being reflexive.
	 *
	 * By contrast, a covering relation need not be transitive, even though adding transitive pairs is also always
	 * sound. Hence, if adding pairs to ensure transitivity is possible with reasonable efficiency, implementations are
	 * encouraged to do so.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <S>
	 *            The type of states.
	 */
	@FunctionalInterface
	public interface ICoveringRelation<S> extends IGeneralizedCoveringRelation<S> {
		/**
		 * Determines if a given old (already explored) state covers a given new (possibly unexplored) state.
		 *
		 * @param oldState
		 *            a previously explored state
		 * @param newState
		 *            a state about to be explored
		 * @return true if the old state covers the new state, false otherwise
		 */
		boolean covers(S oldState, S newState);

		@Override
		default Set<S> coveringStates(final Set<S> oldStates, final S newState) {
			final var covering = oldStates.stream().filter(o -> covers(o, newState)).findAny();
			if (covering.isEmpty()) {
				return null;
			}
			return Set.of(covering.get());
		}
	}

	@FunctionalInterface
	public interface IGeneralizedCoveringRelation<S> {
		/**
		 * Determines if some given old (already explored) states jointly cover a given new (possibly unexplored) state.
		 *
		 * @param oldStates
		 *            a set of previously explored states
		 * @param newState
		 *            a state about to be explored
		 * @return a subset of old states that jointly cover the new state; or null if no such set could be found.
		 */
		Set<S> coveringStates(Set<S> oldStates, S newState);

		/**
		 * Can be used to optimize the search for old covering states. If a state s1 covers a state s2, then the call
		 * {@code Objects.equals(getKey(s1), getKey(s2))} should return true.
		 *
		 * The default implementation simply returns the same constant value (null) for all inputs.
		 *
		 * @param state
		 *            A state
		 * @return any object (or null), as long as the above constraint holds
		 */
		default Object getKey(final S state) {
			return null;
		}
	}
}
