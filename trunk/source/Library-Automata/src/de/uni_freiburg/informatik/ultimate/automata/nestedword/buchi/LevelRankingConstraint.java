/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

/**
 * Constraints that define a set of LevelRankingStates.
 * <ul>
 * <li>mLevelRanking represents an upper bound for ranks of LevelRankingStates defined by this LevelRankingConstraints.
 * <li>A DoubleDecker is in LevelRankingState.mO iff (it is in LevelRankingConstraints.mO and it has an even level rank)
 * </ul>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class LevelRankingConstraint<LETTER, STATE> extends LevelRankingState<LETTER, STATE> {

	/**
	 * Elements of this enum are used to define when an individual state (resp.
	 * {@link DoubleDecker}) inside a macro state is a candidate for a voluntary
	 * decrease from an even to an odd rank. Note that voluntary rank decreases are
	 * implicitly restricted to states that are non-accepting.
	 *
	 */
	public enum VoluntaryRankDecrease {
		/**
		 * All predecessor of the individual state (resp.
		 * {@link DoubleDecker}) that have an even rank are accepting.
		 */
		ALL_EVEN_PREDECESSORS_ARE_ACCEPTING,
		/**
		 * The set O of the predecessor macro state is empty.
		 */
		PREDECESSOR_HAS_EMPTY_O,
		/**
		 * The individual state (resp. {@link DoubleDecker}) would be in the set O of
		 * the macro state. Hence a decrease the rank ensures that the state can escape
		 * from the set O.
		 */
		ALLOWS_O_ESCAPE,
		/**
		 * Conjunction of two other elements.
		 */
		ALLOWS_O_ESCAPE_AND_ALL_EVEN_PREDECESSORS_ARE_ACCEPTING,
		/**
		 * No additional restriction to the implicit restrictions for voluntary rank
		 * decreases.
		 */
		ALWAYS,
	}


	protected final LevelRankingState<LETTER, STATE> mPredecessorLrs;
	private final boolean mPredecessorLrsIsPowersetComponent;
	protected final HashRelation3<StateWithRankInfo<STATE>, STATE, DoubleDecker<StateWithRankInfo<STATE>>> mPredecessors = new HashRelation3<>();

	public static <LETTER, STATE> boolean areAllEvenPredecessorsAccepting(final DoubleDecker<StateWithRankInfo<STATE>> dd, final LevelRankingConstraint<LETTER, STATE> lrc) {
		if (lrc instanceof LevelRankingConstraintDrdCheck) {
			return ((LevelRankingConstraintDrdCheck<LETTER, STATE>) lrc).nonAcceptingPredecessorsWithEvenRanksIsEmpty(dd.getDown(), dd.getUp().getState());
		} else {
			throw new UnsupportedOperationException("information unavailable");
		}

	}

	public static <LETTER, STATE> boolean predecessorHasEmptyO(final DoubleDecker<StateWithRankInfo<STATE>> dd, final LevelRankingConstraint<LETTER, STATE> lrc) {
		return lrc.predecessorHasEmptyO();
	}

	public static <LETTER, STATE> boolean allowsOEscape(final DoubleDecker<StateWithRankInfo<STATE>> dd, final LevelRankingConstraint<LETTER, STATE> lrc) {
		return lrc.inO(dd.getDown(), dd.getUp().getState());
	}






	protected final boolean mPredecessorOwasEmpty;

	private final int mUserDefinedMaxRank;
	/**
	 * if !mUseDoubleDeckers we always use getEmptyStackState() as down state to obtain sets of states instead of sets
	 * of DoubleDeckers.
	 */
	private final boolean mUseDoubleDeckers;

	/**
	 * Information if the direct predecessor of a DoubleDecker was accepting. If this information is used by the
	 * LevelRankingGenerator.
	 */
	private final Set<DoubleDecker<StateWithRankInfo<STATE>>> mSomePredecessorWasAccepting = new HashSet<>();



	public boolean predecessorHasEmptyO() {
		return mPredecessorOwasEmpty;
	}

	public LevelRankingConstraint(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final boolean predecessorOwasEmpty, final int userDefinedMaxRank, final boolean useDoubleDeckers,
			final boolean predecessorLrsIsPowersetComponent, final LevelRankingState<LETTER, STATE> predecessorLrs) {
		super(operand);
		mPredecessorOwasEmpty = predecessorOwasEmpty;
		mUserDefinedMaxRank = userDefinedMaxRank;
		mUseDoubleDeckers = useDoubleDeckers;
		mPredecessorLrs = predecessorLrs;
		mPredecessorLrsIsPowersetComponent = predecessorLrsIsPowersetComponent;
	}

	/**
	 * Constructor for the constraint that is only satisfied by the non accepting sink state.
	 */
	public LevelRankingConstraint() {
		super();
		mPredecessorOwasEmpty = false;
		mUserDefinedMaxRank = -1;
		mUseDoubleDeckers = true;
		mPredecessorLrsIsPowersetComponent = true;
		mPredecessorLrs = null;
	}

	void internalSuccessorConstraints(final IFkvState<LETTER, STATE> state, final LETTER symbol) {
		for (final StateWithRankInfo<STATE> downState : state.getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : state.getUpStates(downState)) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand
						.internalSuccessors(upState.getState(), symbol)) {
					addConstraint(downState, trans.getSucc(), new DoubleDecker<>(downState, upState));
				}
			}
		}
	}

	void callSuccessorConstraints(final IFkvState<LETTER, STATE> state, final LETTER symbol) {
		for (final StateWithRankInfo<STATE> downState : state.getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : state.getUpStates(downState)) {
				for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(upState.getState(),
						symbol)) {
					// if !mUseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					final StateWithRankInfo<STATE> succDownState =
							mUseDoubleDeckers ? upState : new StateWithRankInfo<>(mOperand.getEmptyStackState());
					addConstraint(succDownState, trans.getSucc(), new DoubleDecker<>(downState, upState));
				}
			}
		}
	}

	void returnSuccessorConstraints(final IFkvState<LETTER, STATE> state, final IFkvState<LETTER, STATE> hier,
			final LETTER symbol) {
		for (final StateWithRankInfo<STATE> hierDown : hier.getDownStates()) {
			for (final StateWithRankInfo<STATE> hierUp : hier.getUpStates(hierDown)) {
				returnSuccessorConstraintsHelper(state, symbol, hierDown, hierUp);
			}
		}
	}

	@SuppressWarnings("squid:S1698")
	private void returnSuccessorConstraintsHelper(final IFkvState<LETTER, STATE> state, final LETTER symbol,
			final StateWithRankInfo<STATE> hierDown, final StateWithRankInfo<STATE> hierUp) {
		if (state.getDownStates().isEmpty()) {
			return;
			//throw new AssertionError();
		}
		StateWithRankInfo<STATE> downState;
		if (mUseDoubleDeckers) {
			if (!state.getDownStates().contains(hierUp)) {
				return;
			}
			downState = hierUp;
		} else {
			assert state.getDownStates().size() == 1;
			// equality intended here
			assert state.getDownStates().iterator().next() == mOperand.getEmptyStackState();
			// if !mUseDoubleDeckers we always use getEmptyStackState()
			// as down state to obtain sets of states instead of
			// sets of DoubleDeckers.
			downState = new StateWithRankInfo<>(mOperand.getEmptyStackState());
		}
		final Iterable<StateWithRankInfo<STATE>> upStates = state.getUpStates(downState);
		addReturnSuccessorConstraintsGivenDownState(state, downState, upStates, hierDown, hierUp, symbol);
	}

	@SuppressWarnings("squid:S1698")
	private void addReturnSuccessorConstraintsGivenDownState(final IFkvState<LETTER, STATE> state,
			final StateWithRankInfo<STATE> downState, final Iterable<StateWithRankInfo<STATE>> upStates,
			final StateWithRankInfo<STATE> hierDown, final StateWithRankInfo<STATE> hierUp, final LETTER symbol) {
		for (final StateWithRankInfo<STATE> stateUp : upStates) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(stateUp.getState(),
					hierUp.getState(), symbol)) {
				// equality intended here
				assert mUseDoubleDeckers || hierDown == mOperand.getEmptyStackState();
				addConstraint(hierDown, trans.getSucc(),
						new DoubleDecker<StateWithRankInfo<STATE>>(downState, stateUp));
			}
		}
	}

	/**
	 * Add constraint to the double decker (down,up). This constraints are only
	 * obtained from incoming transitions. Further constraints (odd rank only
	 * allowed for non-finals or state in o if not odd) are added later.
	 */
	protected void addConstraint(final StateWithRankInfo<STATE> downState, final STATE upState,
			final DoubleDecker<StateWithRankInfo<STATE>> predDD) {
		mPredecessors.addTriple(downState, upState, predDD);
		Integer predecessorRank;
		if (mPredecessorLrsIsPowersetComponent) {
			predecessorRank = mUserDefinedMaxRank;
		} else {
			predecessorRank = mPredecessorLrs.getRank(predDD.getDown(), predDD.getUp().getState());
		}

		boolean predecessorIsInO;
		if (mPredecessorLrsIsPowersetComponent) {
			predecessorIsInO = false;
		} else {
			predecessorIsInO = mPredecessorLrs.inO(predDD.getDown(), predDD.getUp().getState());
		}

		final boolean predecessorIsAccepting = mOperand.isFinal(predDD.getUp().getState());

		// This method is very similar to addRank(), but it does not
		// override a rank that was already set (instead takes the minimum)
		// and one assert is missing.
		assert predecessorRank != null;
		HashMap<STATE, Integer> up2rank = mLevelRanking.get(downState);
		if (up2rank == null) {
			up2rank = new HashMap<>();
			mLevelRanking.put(downState, up2rank);
		}
		final Integer oldRank = up2rank.get(upState);
		if (oldRank == null || oldRank > predecessorRank) {
			up2rank.put(upState, predecessorRank);
		}
		final boolean oCandidate = predecessorIsInO || mPredecessorOwasEmpty;
		if (oCandidate) {
			addToO(downState, upState);
		}
		if (mHighestRank < predecessorRank) {
			mHighestRank = predecessorRank;
		}
		if (predecessorIsAccepting) {
			mSomePredecessorWasAccepting
					.add(new DoubleDecker<>(downState, new StateWithRankInfo<>(upState, predecessorRank, oCandidate)));
		}
	}

	public Set<DoubleDecker<StateWithRankInfo<STATE>>> getPredecessorWasAccepting() {
		return mSomePredecessorWasAccepting;
	}

//	public List<DoubleDecker<StateWithRankInfo<STATE>>> getDoubleDeckersEligibleForVoluntaryRankDecrease(
//			boolean voluntaryRankDecreaseOnlyIfPredecessorWasAccepting,
//			boolean volutaryRankDecreaseOnlyIfEnablesEscapeFromO) {
//		ArrayList<DoubleDecker<StateWithRankInfo<STATE>>> result = new ArrayList();
//		if (voluntaryRankDecreaseOnlyIfPredecessorWasAccepting) {
//			for (DoubleDecker<StateWithRankInfo<STATE>> dd : mPredecessorWasAccepting) {
//				boolean isElibi
//			}
//		} else {
//			throw new UnsupportedOperationException("unsupported. However not required for any good complementation");
//		}
//		return result;
//	}

	private boolean isEligibleForVoluntaryRankDecrease(final boolean voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting,
			final boolean voluntaryRankDecreaseOnlyIfEnablesEscapeFromO, final boolean omitConfluenceEnforcedDelayedRankDecrease,
			final DoubleDecker<StateWithRankInfo<STATE>> dd) {
		if (omitConfluenceEnforcedDelayedRankDecrease) {
			throw new AssertionError("unable to check, use subclass");
		}
		boolean isEligible;
		// voluntary decrease makes only sense for even ranks
		isEligible = isEven(dd.getUp().getRank());
		// if state is accepting we are not allowed to decrease to an odd rank
		isEligible &= mOperand.isFinal(dd.getUp().getState());
		// optimization used in all effective complementations: do voluntary
		// decrease only immediately after some predecessor was visiting an accepting
		// state
		isEligible &= (!voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting
				|| mSomePredecessorWasAccepting.contains(dd));
		// optimization used in some effective complementations: do voluntary
		// decrease only for states that would be in the set O if we would
		// not decrease their rank to an odd rank.
		// This optimization is incompatible to the original NCSB complementation.
		isEligible &= (!voluntaryRankDecreaseOnlyIfEnablesEscapeFromO || dd.getUp().isInO());
		return isEligible;
	}

	public boolean allEvenPredecessorsAreAcceptingOrNotInO(final StateWithRankInfo<STATE> downState,
			final STATE upState) {
		final Set<Integer> result = new HashSet<>();
		for (final DoubleDecker<StateWithRankInfo<STATE>> pred : mPredecessors.projectToTrd(downState, upState)) {
			if (isEven(pred.getUp().getRank())) {
				if (!mOperand.isFinal(pred.getUp().getState()) && pred.getUp().isInO()) {
					return false;
				}
			}
		}
		return true;
	}


}
