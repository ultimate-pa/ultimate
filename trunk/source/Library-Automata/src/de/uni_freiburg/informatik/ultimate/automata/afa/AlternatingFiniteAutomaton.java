package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.afa.AlternatingFiniteAutomaton.AfaState.StateType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;

public class AlternatingFiniteAutomaton<L, S> {

	// TODO: positional order? OrderAutomaton (similar to ParameterizedPreferenceOrderAutomaton)
	private final IDfsOrder<L, S> mOrder;
	private final Set<L> mAlphabet;
	private Set<AfaState> mStates;
	private Set<AfaState> mInitialStates;
	private Set<AfaState> mFinalStates;
	// mUnderlying should accept the words rho<ab>sigma s.t. (rho,a,b,sigma) in I
	// in contrast to the current version in the paper, we need to flip the accepting states in the AFA reduction and
	// use a conjunction instead of a disjunction when quantifying over the underlying transitions
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mUnderlying;
	private final Map<StateKey<L, S>, AfaState> mStateCache = new HashMap<>();

	// Right now it follows the definition in our paper. However, I think we need the program automaton (or the current
	// abstraction?) as an input and TRACK should actually track the states of this automaton instead
	// before the search, do an intersection of the current abstraction (transformed to an AFA) with the reduction AFA
	public AlternatingFiniteAutomaton(final IDfsOrder<L, S> order, final Set<L> alphabet,
			final INwaOutgoingLetterAndTransitionProvider<L, S> underlying) {
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

	// mUnderlying non-deterministic? yes, disjunctions
	// Can it really be an iterable? How does the DFS know the formula? No, return a BDD.
	public Iterable<AfaTransition<L>> getSuccessors(final AfaState state, final L letter) {
		// TODO complete
		final L sleepLetter = state.mSleepletter;
		final S underlyingState = state.mState;
		final Iterable<OutgoingInternalTransition<L, S>> underylingTransitions =
				mUnderlying.internalSuccessors(underlyingState, letter);
		final Set<AfaTransition<L>> transitions = new HashSet<>();
		AlternatingFiniteAutomaton<L, S>.AfaState succ;

		switch (state.mType) {
		case TRACK:
			for (final OutgoingInternalTransition<L, S> t : underylingTransitions) {
				succ = getOrConstructState(StateType.TRACK, null, t.getSucc());
				transitions.add(new AfaTransition<>(letter, succ));
			}
			for (final L letter2 : mAlphabet) {
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

	// not sure if this is a good approach, but that way we can construct conjuncts and disjuncts as we need to
	/*
	 * // conjunction of two IAfaTransitions class AndTransition<L3> implements IAfaTransition<L3> {
	 * Set<IAfaTransition<L3>> mTransitions;
	 *
	 * public AndTransition(final Set<IAfaTransition<L3>> transitions) { mTransitions = transitions; }
	 *
	 * @Override public Set<IAfaTransition<L3>> getTransitions() { return mTransitions; } }
	 *
	 * // disjunction of two IAfaTransitions class OrTransition<L3> implements IAfaTransition<L3> {
	 * Set<IAfaTransition<L3>> mTransitions;
	 *
	 * public OrTransition(final Set<IAfaTransition<L3>> transitions) { mTransitions = transitions; }
	 *
	 * @Override public Set<IAfaTransition<L3>> getTransitions() { return mTransitions; } }
	 *
	 * // add constants for true and false?
	 */
}
