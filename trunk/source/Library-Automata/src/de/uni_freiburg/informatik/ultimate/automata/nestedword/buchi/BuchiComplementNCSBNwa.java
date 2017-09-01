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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.SetOfStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaSuccessorStateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Implements the following paper.
 * 2017TACAS - Blahoudek,Heizmann,Schewe,Strejček,Tsai - Complementing Semi-deterministic Büchi Automata
 * 
 * If we mention line numbers, we refer to numbers used in the orginal publication.
 * https://link.springer.com/chapter/10.1007/978-3-662-49674-9_49

 * TODO: More documentation.
 * Ranks and inO information translate to the NCSB quadruple as follows.
 * state has rank 3 == state is in N
 * state has rank 2 == state is in C
 * state has rank 1 == state is in S
 * state is in O == state is in B
 * 
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiComplementNCSBNwa<LETTER, STATE> implements INwaSuccessorStateProvider<LETTER, STATE> {
	private static final int MAGIC_RANK = 7777;
	private static final int BARELY_COVERED_MAX_RANK = 3;
	private static final Integer RANK_FINAL = Integer.valueOf(2);
	private static final Integer RANK_NONFINAL = Integer.valueOf(3);

	/**
	 * Heuristic where we move to accepting sink already from states with nonempty difference C\F. Warning: yet this is
	 * only implemented for internal transitions.
	 */
	private static final boolean EARLY_SINK_HEURISTIC = false;

	private final AutomataLibraryServices mServices;
	
	private final SetOfStates<STATE> mSetOfStates;

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;

	private final IBuchiComplementNcsbStateFactory<STATE> mStateFactory;

	private final StateWithRankInfo<STATE> mEmptyStackStateWri;

	/**
	 * Maps NCSB state to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState<LETTER, STATE>, STATE> mDet2res = new HashMap<>();

	/**
	 * Maps a state in resulting automaton to the NCSB state for which it was created.
	 */
	private final Map<STATE, LevelRankingState<LETTER, STATE>> mRes2det = new HashMap<>();

	private final BarelyCoveredLevelRankingsGenerator<LETTER, STATE> mBclrg;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public BuchiComplementNCSBNwa(final AutomataLibraryServices services,
			final IBuchiComplementNcsbStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		mServices = services;
		mOperand = operand;
		mStateFactory = stateFactory;
		mSetOfStates = new SetOfStates<>(mStateFactory.createEmptyStackState());
		mEmptyStackStateWri = new StateWithRankInfo<>(mSetOfStates.getEmptyStackState());
		mBclrg = new BarelyCoveredLevelRankingsGenerator<>(mServices, mOperand, BARELY_COVERED_MAX_RANK, false, true,
				false, false, false);
		constructInitialState();
	}

	private void constructInitialState() {
		final LevelRankingState<LETTER, STATE> lvlrk = new LevelRankingState<>(mOperand);
		for (final STATE state : mOperand.getInitialStates()) {
			if (mOperand.isFinal(state)) {
				lvlrk.addRank(mEmptyStackStateWri, state, RANK_FINAL, true);
			} else {
				lvlrk.addRank(mEmptyStackStateWri, state, RANK_NONFINAL, false);
			}
		}
		getOrAdd(true, lvlrk);
	}

	/**
	 * Return state of result automaton that represents detState. If no such state was constructed yet, construct it.
	 */
	private STATE getOrAdd(final boolean isInitial, final LevelRankingState<LETTER, STATE> lvlrk) {
		STATE resState = mDet2res.get(lvlrk);
		if (resState == null) {
			resState = mStateFactory.buchiComplementNcsb(lvlrk);
			mDet2res.put(lvlrk, resState);
			mRes2det.put(resState, lvlrk);
			final boolean isFinal = !lvlrk.isNonAcceptingSink() && lvlrk.isOempty();
			mSetOfStates.addState(isInitial, isFinal, resState);
		} else {
			assert !isInitial;
		}
		return resState;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mSetOfStates.getInitialStates();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mSetOfStates.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mSetOfStates.isAccepting(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mSetOfStates.getEmptyStackState();
	}


	private LevelRankingConstraintDrdCheck<LETTER, STATE> computeSuccLevelRankingConstraint_Internal(final STATE state,
			final LETTER letter) {
		final LevelRankingState<LETTER, STATE> lvlrkState = mRes2det.get(state);
		if (lvlrkState.isNonAcceptingSink()) {
			return new LevelRankingConstraintDrdCheck<>();
		}
		final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint =
				new LevelRankingConstraintDrdCheck<>(mOperand, lvlrkState.isOempty(), MAGIC_RANK, true);
		boolean transitionWouldAnnihilateEvenRank = false;
		boolean somePredecessorHasRank1 = false;
		for (final StateWithRankInfo<STATE> downState : lvlrkState.getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : lvlrkState.getUpStates(downState)) {
				if (upState.getRank() == 1) {
					somePredecessorHasRank1 = true;
				}
				boolean hasSuccessor = false;
				for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand
						.internalSuccessors(upState.getState(), letter)) {
					hasSuccessor = true;
					constraint.addConstraint(downState, trans.getSucc(), upState.getRank(), upState.isInO(),
							mOperand.isFinal(upState.getState()));
				}
				if (transitionWouldAnnihilateEvenRank(upState, hasSuccessor)) {
					transitionWouldAnnihilateEvenRank = true;
				}
			}
		}
		if (returnEmptyLrConstraint(constraint, transitionWouldAnnihilateEvenRank, somePredecessorHasRank1)) {
			return new LevelRankingConstraintDrdCheck<>();
		}
		return constraint;
	}

	private boolean returnEmptyLrConstraint(final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final boolean transitionWouldAnnihilateEvenRank, final boolean somePredecessorHasRank1) {
		if (EARLY_SINK_HEURISTIC) {
			if (transitionWouldAnnihilateEvenRank && !constraint.isEmpty()) {
				return true;
			}
			if (somePredecessorHasRank1 && constraint.isEmpty()) {
				return true;
			}
		} else {
			if (transitionWouldAnnihilateEvenRank) {
				return true;
			}
		}
		return false;
	}

	/**
	 * This method is used to check the condition of the fifth bullet in the
	 * construction of the transition relation of the complement automaton
	 * (lines 12 and 13 on page 7 of the paper).
	 * If a state (here upState) is in the set C (i.e. has an even rank in our
	 * encoding), is not final (which would have enforced membership in C),
	 * and does not have a successor an outgoing transition would be 
	 * superficial. This is because in our construction we already track
	 * a run in which we moved the state to the set S earlier. 
	 */
	private boolean transitionWouldAnnihilateEvenRank(final StateWithRankInfo<STATE> upState,
			final boolean hasSuccessor) {
		return !hasSuccessor && !mOperand.isFinal(upState.getState()) && LevelRankingState.isEven(upState.getRank());
	}

	private LevelRankingConstraintDrdCheck<LETTER, STATE> computeSuccLevelRankingConstraint_Call(final STATE state,
			final LETTER letter) {
		final LevelRankingState<LETTER, STATE> lvlrkState = mRes2det.get(state);
		if (lvlrkState.isNonAcceptingSink()) {
			return new LevelRankingConstraintDrdCheck<>();
		}
		final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint =
				new LevelRankingConstraintDrdCheck<>(mOperand, lvlrkState.isOempty(), MAGIC_RANK, true);
		for (final StateWithRankInfo<STATE> downState : lvlrkState.getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : lvlrkState.getUpStates(downState)) {
				boolean hasSuccessor = false;
				for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(upState.getState(),
						letter)) {
					hasSuccessor = true;
					constraint.addConstraint(upState, trans.getSucc(), upState.getRank(), upState.isInO(),
							mOperand.isFinal(upState.getState()));
				}
				if (transitionWouldAnnihilateEvenRank(upState, hasSuccessor)) {
					return new LevelRankingConstraintDrdCheck<>();
				}
			}
		}
		return constraint;
	}

	private LevelRankingConstraintDrdCheck<LETTER, STATE> computeSuccLevelRankingConstraint_Return(final STATE state,
			final STATE hier, final LETTER letter) {
		final LevelRankingState<LETTER, STATE> lvlrkState = mRes2det.get(state);
		if (lvlrkState.isNonAcceptingSink()) {
			return new LevelRankingConstraintDrdCheck<>();
		}
		final LevelRankingState<LETTER, STATE> lvlrkHier = mRes2det.get(hier);
		final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint =
				new LevelRankingConstraintDrdCheck<>(mOperand, lvlrkState.isOempty(), MAGIC_RANK, true);
		for (final StateWithRankInfo<STATE> downHier : lvlrkHier.getDownStates()) {
			for (final StateWithRankInfo<STATE> upHier : lvlrkHier.getUpStates(downHier)) {
				if (!lvlrkState.getDownStates().contains(upHier)) {
					continue;
				}
				final boolean transitionWouldAnnihilateEvenRank =
						computeSuccLevelRankingConstraintReturnHelper(letter, lvlrkState, constraint, downHier, upHier);
				if (transitionWouldAnnihilateEvenRank) {
					return new LevelRankingConstraintDrdCheck<>();
				}
			}
		}
		return constraint;
	}

	private boolean computeSuccLevelRankingConstraintReturnHelper(final LETTER letter,
			final LevelRankingState<LETTER, STATE> lvlrkState,
			final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint, final StateWithRankInfo<STATE> downHier,
			final StateWithRankInfo<STATE> upHier) {
		for (final StateWithRankInfo<STATE> upState : lvlrkState.getUpStates(upHier)) {
			boolean hasSuccessor = false;
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(upState.getState(),
					upHier.getState(), letter)) {
				hasSuccessor = true;
				constraint.addConstraint(downHier, trans.getSucc(), upState.getRank(), upState.isInO(),
						mOperand.isFinal(upState.getState()));
			}
			if (transitionWouldAnnihilateEvenRank(upState, hasSuccessor)) {
				return true;
			}
		}
		return false;
	}

	private Collection<STATE> computeStates(final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint) {
		/*
		 * This check reflects the fourth bullet in the
		 * construction of the transition relation of the complement automaton
		 * (lines 10 and 11 on page 7 of the paper).
		 * 
		 * If we have a state that has predecessors in the set C and 
		 * predecessors in the set S, the state needs to be in S 
		 * (because we must not go back from S to C).
		 * However, if one predecessor in C is not an accepting state, we
		 * already track a run in which this state was already moved to S
		 * (at some point in time where this run left an accepting state).
		 * Hence these transitions are superficial. 
		 */
		if (constraint.isTargetOfDelayedRankDecrease()) {
			// in this case we do not want to have successor states
			return Collections.emptyList();
		}
		final Collection<LevelRankingState<LETTER, STATE>> succLvls = mBclrg.generateLevelRankings(constraint, false);
		final List<STATE> computedSuccs = new ArrayList<>();
		for (final LevelRankingState<LETTER, STATE> succLvl : succLvls) {
			final STATE resSucc = getOrAdd(false, succLvl);
			computedSuccs.add(resSucc);
		}
		return computedSuccs;
	}



	@Override
	public int size() {
		return mSetOfStates.getStates().size();
	}


	@Override
	public String sizeInformation() {
		return "size Information not available";
	}

	@Override
	public Collection<STATE> internalSuccessors(final STATE state, final LETTER letter) {
		final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint =
				computeSuccLevelRankingConstraint_Internal(state, letter);
		final Collection<STATE> computedSuccs = computeStates(constraint);
		return computedSuccs;
	}

	@Override
	public Collection<STATE> callSuccessors(final STATE state, final LETTER letter) {
		final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint =
				computeSuccLevelRankingConstraint_Call(state, letter);
		final Collection<STATE> computedSuccs = computeStates(constraint);
		return computedSuccs;
	}

	@Override
	public Collection<STATE> returnSuccessorsGivenHier(final STATE state, final STATE hier, final LETTER letter) {
		final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint =
				computeSuccLevelRankingConstraint_Return(state, hier, letter);
		final Collection<STATE> computedSuccs = computeStates(constraint);
		return computedSuccs;
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException();
	}
}
