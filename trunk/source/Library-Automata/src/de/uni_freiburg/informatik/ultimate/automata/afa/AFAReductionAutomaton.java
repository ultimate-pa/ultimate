/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.afa.AFAReductionAutomaton.AfaState.StateType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;

public class AFAReductionAutomaton<L, S> /* extends AlternatingFiniteAutomaton<L, S> */ {

	// TODO: positional order? OrderAutomaton (similar to ParameterizedPreferenceOrderAutomaton)
	private final IDfsOrder<L, S> mOrder;
	private final Set<L> mAlphabet;
	private Set<AfaState> mStates;
	private Set<AfaState> mInitialStates;
	private Set<AfaState> mFinalStates;
	final BddManager<AfaState> mBddManager = new BddManager<>();
	// mUnderlying should accept the words rho<ab>sigma s.t. (rho,a,b,sigma) in I
	// TODO: in contrast to the current version in the paper, we need to flip the accepting states in the AFA reduction
	// and use a conjunction instead of a disjunction when quantifying over the underlying transitions
	private final IndependencyAutomaton<L, S> mUnderlying;
	private final Map<StateKey<L, S>, AfaState> mStateCache = new HashMap<>();

	// Right now it follows the definition in our paper. However, I think we need the program automaton (or the current
	// abstraction?) as an input and TRACK should actually track the states of this automaton instead
	// before the search, do an intersection of the current abstraction (transformed to an AFA) with the reduction AFA
	public AFAReductionAutomaton(final IDfsOrder<L, S> order, final Set<L> alphabet,
			final IndependencyAutomaton<L, S> underlying) {
		mOrder = order;
		mAlphabet = alphabet;
		mUnderlying = underlying;
		constructInitialStates();
	}

	private void constructInitialStates() {
		final Iterable<S> underylingInitialStates = mUnderlying.getInitialStates();
		for (final S state : underylingInitialStates) {
			mInitialStates.add(new AfaState(StateType.TRACK, null, state));
		}
	}

	public Set<L> getAlphabet() {
		return mAlphabet;
	}

	public int size() {
		return mStates.size();
	}

	public Iterable<AfaState> getInitialStates() {
		return mInitialStates;
	}

	public boolean isInitial(final AfaState state) {
		return mInitialStates.contains(state);
	}

	public boolean isFinal(final AfaState state) {
		return mFinalStates.contains(state);
	}

	// TODO: implement
	public Bdd<AfaState> getSuccessors(final AfaState state, final L letter) {

		final L sleepLetter = state.mSleepletter;
		final S underlyingState = state.mState;
		final Iterable<OutgoingInternalTransition<L, S>> underylingTransitions =
				mUnderlying.internalSuccessors(underlyingState, letter);
		Bdd<AfaState> bddResult = mBddManager.getFalse();
		AfaState succ;

		switch (state.mType) {
		case TRACK:
			for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
				succ = getOrConstructState(StateType.TRACK, null, t.getSucc());
				bddResult = bddResult.or(mBddManager.variable(succ));
			}
			Bdd<AfaState> bddConjunction = mBddManager.getTrue();
			for (final L letter2 : mAlphabet) {
				Bdd<AfaState> bddDisjunction = mBddManager.getFalse();
				if (mOrder.getOrder(underlyingState).compare(letter, letter2) < 0) {
					for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
						// TODO: what if the order is positional? Positional w.r.t which state? TODO: OrderAutomaton
						succ = getOrConstructState(StateType.SLEEP, letter2, t.getSucc());
						bddDisjunction = bddDisjunction.or(mBddManager.variable(succ));
					}
					// TODO: what about the extra symbol <ab>?
					final Optional<L> specialSymbol = mUnderlying.getSpecialSymbol(letter, sleepLetter);
					if (specialSymbol.isPresent()) {
						final L symbol = specialSymbol.get();
						for (final OutgoingInternalTransition<L, S> t : mUnderlying.internalSuccessors(underlyingState,
								symbol)) {
							succ = getOrConstructState(StateType.WAIT, letter2, t.getSucc());
							bddDisjunction = bddDisjunction.or(mBddManager.variable(succ));
						}
					} else {
						// idk
					}
					bddConjunction = bddConjunction.and(bddDisjunction);
				}
			}
			bddResult = bddResult.and(bddConjunction);
			break;
		case SLEEP:
			if (sleepLetter == letter) {
				succ = getOrConstructState(StateType.FALSE, null, null);
				bddResult = mBddManager.variable(succ);
			} else {
				for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
					succ = getOrConstructState(StateType.SLEEP, sleepLetter, t.getSucc());
					bddResult = bddResult.or(mBddManager.variable(succ));
				}
				// TODO: what about the extra symbol <ab>?
				final Optional<L> specialSymbol = mUnderlying.getSpecialSymbol(letter, sleepLetter);
				if (specialSymbol.isPresent()) {
					final L symbol = specialSymbol.get();
					for (final OutgoingInternalTransition<L, S> t : mUnderlying.internalSuccessors(underlyingState,
							symbol)) {
						succ = getOrConstructState(StateType.WAIT, sleepLetter, t.getSucc());
						bddResult = bddResult.or(mBddManager.variable(succ));
					}
				} else {
					// idk
				}
			}
			break;
		case WAIT:
			if (sleepLetter == letter) {
				succ = getOrConstructState(StateType.CHECK, null, underlyingState);
				bddResult = mBddManager.variable(succ);
			} else {
				for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
					succ = getOrConstructState(StateType.WAIT, sleepLetter, t.getSucc());
					bddResult = bddResult.or(mBddManager.variable(succ));
				}
			}
			break;
		case CHECK:
			for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
				succ = getOrConstructState(StateType.CHECK, null, t.getSucc());
				bddResult = bddResult.or(mBddManager.variable(succ));
			}
			break;
		case FALSE:
			// is FALSE actually a state or does it mean "no successors"?
			// If the latter we may use mBddManager.getFalse() instead?
			succ = getOrConstructState(StateType.FALSE, null, null);
			bddResult = mBddManager.variable(succ);
		}
		return bddResult;
	}

	// mUnderlying non-deterministic? yes, disjunctions
	// Can it really be an iterable? How does the DFS know the formula? No, return a BDD.
	public Iterable<AfaTransition<L>> getSuccessors2(final AfaState state, final L letter) {
		// TODO complete
		final L sleepLetter = state.mSleepletter;
		final S underlyingState = state.mState;
		final Iterable<OutgoingInternalTransition<L, S>> underylingTransitions =
				mUnderlying.internalSuccessors(underlyingState, letter);
		final Set<AfaTransition<L>> transitions = new HashSet<>();
		AfaState succ;

		switch (state.mType) {
		case TRACK:
			for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
				succ = getOrConstructState(StateType.TRACK, null, t.getSucc());
				transitions.add(new AfaTransition<>(letter, succ));
			}
			for (final L letter2 : mAlphabet) {
				if (mOrder.getOrder(underlyingState).compare(letter, letter2) < 0) {
				for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
					// TODO: what if the order is positional? Positional w.r.t which state? OrderAutomaton
					if (mOrder.getOrder(underlyingState).compare(letter, letter2) < 0) {
						succ = getOrConstructState(StateType.SLEEP, letter2, t.getSucc());
						transitions.add(new AfaTransition<>(letter, succ));
						// TODO: what about the extra symbol <ab>?
					}
				}
			}
			break;
		case SLEEP:
			if (sleepLetter == letter) {
				succ = getOrConstructState(StateType.FALSE, null, null);
				transitions.add(new AfaTransition<>(letter, succ));
			} else {
				for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
					succ = getOrConstructState(StateType.SLEEP, sleepLetter, t.getSucc());
					transitions.add(new AfaTransition<>(letter, succ));
				}
				// TODO: what about the extra symbol <ab>?
			}
			break;
		case WAIT:
			if (sleepLetter == letter) {
				succ = getOrConstructState(StateType.CHECK, null, underlyingState);
				transitions.add(new AfaTransition<>(letter, succ));
			} else {
				for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
					succ = getOrConstructState(StateType.WAIT, sleepLetter, t.getSucc());
					transitions.add(new AfaTransition<>(letter, succ));
				}
			}
			break;
		case CHECK:
			for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
				succ = getOrConstructState(StateType.CHECK, null, t.getSucc());
				transitions.add(new AfaTransition<>(letter, succ));
			}
			break;
		case FALSE:
			transitions.add(new AfaTransition<>(letter, state));
		}
		return transitions;
	}

	public AfaState getOrConstructState(final StateType type, final L sleepletter, final S state) {

		final StateKey<L, S> key = new StateKey<>(type, sleepletter, state);
		return mStateCache.computeIfAbsent(key, k -> new AfaState(k.type(), k.sleepletter(), k.state()));
	}

	record StateKey<L, S>(StateType type, L sleepletter, S state) {
	}

	class AfaState {
		StateType mType;
		L mSleepletter;
		S mState;

		enum StateType {
			TRACK, SLEEP, WAIT, CHECK, FALSE
		}

		AfaState(final StateType type, final L sleepletter, final S state) {
			mType = type;
			mSleepletter = sleepletter;
			mState = state;
		}

	}

	// maybe not needed anymore
	class AfaTransition<L2> {
		L2 mLetter;
		AfaState mState;

		public AfaTransition(final L2 letter, final AfaState state) {
			mLetter = letter;
			mState = state;
		}

		public L2 getLetter() {
			return mLetter;
		}

		public AfaState getSucc() {
			return mState;
		}
	}
}
