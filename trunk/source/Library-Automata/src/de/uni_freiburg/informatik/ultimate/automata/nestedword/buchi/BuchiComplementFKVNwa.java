/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.SetOfStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaSuccessorStateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementFkvStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Buchi Complementation based on 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BuchiComplementFKVNwa<LETTER, STATE> implements INwaSuccessorStateProvider<LETTER, STATE> {
	private static final int WARN_SIZE_1 = 2;
	private static final int WARN_SIZE_2 = 4;

	/**
	 * Considering O empty for subset component will safe some states.
	 */
	private static final boolean O_IS_EMPTY = true;

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	/**
	 * TODO Allow definition of a maximal rank for cases where you know that this is sound. E.g. if the automaton is
	 * reverse deterministic a maximal rank of 2 is sufficient, see paper of Seth Forgaty.
	 */
	private final int mUserDefinedMaxRank;

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;

	private final SetOfStates<STATE> mSetOfStates;

	private final IBuchiComplementFkvStateFactory<STATE> mStateFactory;

	/**
	 * Maps DeterminizedState to its representative in the resulting automaton.
	 */
	private final Map<DeterminizedState<LETTER, STATE>, STATE> mDet2res = new HashMap<>();

	/**
	 * Maps a state in resulting automaton to the FkvSubsetComponentState for which it was created.
	 */
	private final Map<STATE, FkvSubsetComponentState<LETTER, STATE>> mRes2scs = new HashMap<>();

	/**
	 * Maps a LevelRankingState to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState<LETTER, STATE>, STATE> mLrk2res = new HashMap<>();

	/**
	 * Maps a state in resulting automaton to the LevelRankingState for which it was created.
	 */
	private final Map<STATE, LevelRankingState<LETTER, STATE>> mRes2lrk = new HashMap<>();

	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;

	/**
	 * Highest rank that occured during the construction. Used only for statistics.
	 */
	private int mHighestRank = -1;

	private final MultiOptimizationLevelRankingGenerator<LETTER, STATE, LevelRankingConstraint<LETTER, STATE>> mLevelRankingGenerator;

	private final STATE mSinkState;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @param stateFactory
	 *            state factory
	 * @param optimization
	 *            optimization parameter
	 * @param userDefinedMaxRank
	 *            user-defined maximal rank
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public BuchiComplementFKVNwa(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			final IBuchiComplementFkvStateFactory<STATE> stateFactory, final FkvOptimization optimization,
			final int userDefinedMaxRank) throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mStateFactory = stateFactory;
		mSetOfStates = new SetOfStates<STATE>(mStateFactory.createEmptyStackState());
		mStateDeterminizer = stateDeterminizer;
		mUserDefinedMaxRank = userDefinedMaxRank;
		mLevelRankingGenerator =
				new MultiOptimizationLevelRankingGenerator<>(mServices, mOperand, optimization, userDefinedMaxRank);
		mSinkState = constructSinkState();
	}

	private void constructInitialState() {
		final DeterminizedState<LETTER, STATE> detState = mStateDeterminizer.initialState();
		getOrAdd(detState, true);
	}

	private STATE constructSinkState() {
		final DeterminizedState<LETTER, STATE> detSinkState = new DeterminizedState<>(mOperand);
		final STATE resSinkState = mStateDeterminizer.getState(detSinkState);
		mSetOfStates.addState(false, true, resSinkState);
		mDet2res.put(detSinkState, resSinkState);
		mRes2scs.put(resSinkState, new FkvSubsetComponentState<>(detSinkState));
		return resSinkState;
	}

	/**
	 * Return state of result automaton that represents lrkState. If no such state was constructed yet, construct it.
	 */
	private STATE getOrAdd(final LevelRankingState<LETTER, STATE> lrkState) {
		if (lrkState.isEmpty()) {
			return mSinkState;
		}
		STATE resSucc = mLrk2res.get(lrkState);
		if (resSucc == null) {
			resSucc = mStateFactory.buchiComplementFkv(lrkState);
			assert resSucc != null;
			mSetOfStates.addState(false, lrkState.isOempty(), resSucc);
			mLrk2res.put(lrkState, resSucc);
			mRes2lrk.put(resSucc, lrkState);
			if (this.mHighestRank < lrkState.mHighestRank) {
				this.mHighestRank = lrkState.mHighestRank;
			}
		}
		return resSucc;
	}

	/**
	 * Return state of result automaton that represents detState. If no such state was constructed yet, construct it.
	 */
	private STATE getOrAdd(final DeterminizedState<LETTER, STATE> detState, final boolean isInitial) {
		if (detState.isEmpty()) {
			assert !isInitial : "sink cannot be initial";
			return mSinkState;
		}
		STATE resSucc = mDet2res.get(detState);
		if (resSucc == null) {
			resSucc = mStateDeterminizer.getState(detState);
			assert resSucc != null;
			mSetOfStates.addState(isInitial, false, resSucc);
			mDet2res.put(detState, resSucc);
			mRes2scs.put(resSucc, new FkvSubsetComponentState<>(detState));
		}
		return resSucc;
	}

	public int getHighesRank() {
		return mHighestRank;
	}

	public int getPowersetStates() {
		return mRes2scs.size();
	}

	public int getRankStates() {
		return mRes2lrk.size();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		constructInitialState();
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

	@Override
	public Collection<STATE> internalSuccessors(final STATE state, final LETTER letter) {
		final Collection<STATE> resSuccs = new ArrayList<>();
		final FkvSubsetComponentState<LETTER, STATE> detUp = mRes2scs.get(state);
		if (detUp != null) {
			final DeterminizedState<LETTER, STATE> detSucc =
					mStateDeterminizer.internalSuccessor(detUp.getDeterminizedState(), letter);
			final STATE resSucc = getOrAdd(detSucc, false);
			resSuccs.add(resSucc);

			internalSuccessorsHelper(state, letter, resSuccs, detUp, O_IS_EMPTY, true, null, WARN_SIZE_1);
		}
		final LevelRankingState<LETTER, STATE> complUp = mRes2lrk.get(state);
		if (complUp != null) {
			internalSuccessorsHelper(state, letter, resSuccs, complUp, complUp.isOempty(), false, complUp, WARN_SIZE_2);
		}
		return resSuccs;
	}

	private void internalSuccessorsHelper(final STATE state, final LETTER letter, final Collection<STATE> resSuccs,
			final IFkvState<LETTER, STATE> detUp, final boolean isEmpty, final boolean predecessorIsSubsetComponent,
			final LevelRankingState<LETTER, STATE> predUp, final int warnSize) {
		final LevelRankingConstraint<LETTER, STATE> constraints = getLevelRankingConstraintDrdCheck(isEmpty,
				predecessorIsSubsetComponent, predUp);
		constraints.internalSuccessorConstraints(detUp, letter);
		final Collection<LevelRankingState<LETTER, STATE>> result =
				generateLevelRankings(predecessorIsSubsetComponent, constraints);
		if (result.size() > warnSize && mLogger.isWarnEnabled()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new ToolchainCanceledException(this.getClass());
			}
			// TODO Christian 2016-08-19: Writes "bigX" to logger on <tt>WARN</tt> level in a loop, i.e., spams a lot.
			mLogger.warn("big" + result.size());
		}
		for (final LevelRankingState<LETTER, STATE> complSucc : result) {
			final STATE resSucc = getOrAdd(complSucc);
			resSuccs.add(resSucc);
		}
	}


	@Override
	public Collection<STATE> callSuccessors(final STATE state, final LETTER letter) {
		final Collection<STATE> resSuccs = new ArrayList<>();
		final FkvSubsetComponentState<LETTER, STATE> detUp = mRes2scs.get(state);
		if (detUp != null) {
			final DeterminizedState<LETTER, STATE> detSucc =
					mStateDeterminizer.callSuccessor(detUp.getDeterminizedState(), letter);
			final STATE resSucc = getOrAdd(detSucc, false);
			resSuccs.add(resSucc);

			callSuccessorsHelper(state, letter, resSuccs, detUp, O_IS_EMPTY, true, null);
		}
		final LevelRankingState<LETTER, STATE> complUp = mRes2lrk.get(state);
		if (complUp != null) {
			callSuccessorsHelper(state, letter, resSuccs, complUp, complUp.isOempty(), false, complUp);
		}
		return resSuccs;
	}

	private void callSuccessorsHelper(final STATE state, final LETTER letter, final Collection<STATE> resSuccs,
			final IFkvState<LETTER, STATE> fkvState, final boolean isEmpty,
			final boolean predecessorIsSubsetComponent,
			final LevelRankingState<LETTER, STATE> predUp) {
		final LevelRankingConstraint<LETTER, STATE> constraints = getLevelRankingConstraintDrdCheck(isEmpty,
				predecessorIsSubsetComponent, predUp);
		constraints.callSuccessorConstraints(fkvState, letter);
		final Collection<LevelRankingState<LETTER, STATE>> result =
				generateLevelRankings(predecessorIsSubsetComponent, constraints);
		for (final LevelRankingState<LETTER, STATE> complSucc : result) {
			final STATE resSucc = getOrAdd(complSucc);
			resSuccs.add(resSucc);
		}
	}


	@Override
	public Collection<STATE> returnSuccessorsGivenHier(final STATE state, final STATE hier, final LETTER letter) {
		final Collection<STATE> resSuccs = new ArrayList<>();
		final FkvSubsetComponentState<LETTER, STATE> detUp = mRes2scs.get(state);
		final FkvSubsetComponentState<LETTER, STATE> detDown = mRes2scs.get(hier);
		if (detUp != null) {
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer
					.returnSuccessor(detUp.getDeterminizedState(), detDown.getDeterminizedState(), letter);
			final STATE resSucc = getOrAdd(detSucc, false);
			resSuccs.add(resSucc);

			returnSuccessorsHelper(state, hier, letter, resSuccs, detUp, detDown, O_IS_EMPTY, true, null);
		}
		final LevelRankingState<LETTER, STATE> complUp = mRes2lrk.get(state);
		IFkvState<LETTER, STATE> complDown;
		if (mRes2scs.containsKey(hier)) {
			complDown = mRes2scs.get(hier);
		} else {
			assert mRes2lrk.containsKey(hier);
			complDown = mRes2lrk.get(hier);
		}
		if (complUp != null) {
			returnSuccessorsHelper(state, hier, letter, resSuccs, complUp, complDown, complUp.isOempty(), false, complUp);
		}
		return resSuccs;
	}


	private void returnSuccessorsHelper(final STATE state, final STATE hier, final LETTER letter,
			final Collection<STATE> resSuccs, final IFkvState<LETTER, STATE> fkvUp,
			final IFkvState<LETTER, STATE> fkvDown, final boolean isEmpty, final boolean predecessorIsSubsetComponent,
			final LevelRankingState<LETTER, STATE> predUp) {
		final LevelRankingConstraint<LETTER, STATE> constraints = getLevelRankingConstraintDrdCheck(isEmpty, predecessorIsSubsetComponent, predUp);
		constraints.returnSuccessorConstraints(fkvUp, fkvDown, letter);
		final Collection<LevelRankingState<LETTER, STATE>> result =
				generateLevelRankings(predecessorIsSubsetComponent, constraints);
		for (final LevelRankingState<LETTER, STATE> complSucc : result) {
			final STATE resSucc = getOrAdd(complSucc);
			resSuccs.add(resSucc);
		}
	}

	private Collection<LevelRankingState<LETTER, STATE>> generateLevelRankings(
			final boolean predecessorIsSubsetComponent, final LevelRankingConstraint<LETTER, STATE> constraints) {
		return mLevelRankingGenerator.generateLevelRankings(constraints, predecessorIsSubsetComponent);
	}

	private LevelRankingConstraint<LETTER, STATE> getLevelRankingConstraintDrdCheck(final boolean isEmpty,
			final boolean predecessorIsSubsetComponent, final LevelRankingState<LETTER, STATE> predecessorLrs) {
		return new LevelRankingConstraintDrdCheck<>(mOperand, isEmpty, mUserDefinedMaxRank,
				mStateDeterminizer.useDoubleDeckers(), predecessorIsSubsetComponent, predecessorLrs);
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
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException();
	}






}
