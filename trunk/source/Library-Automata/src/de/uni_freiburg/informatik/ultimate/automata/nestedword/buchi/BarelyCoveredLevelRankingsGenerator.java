/*
 * Copyright (C) 2009-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2016 University of Freiburg
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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.PowersetIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO documentation.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BarelyCoveredLevelRankingsGenerator<LETTER, STATE>
		extends LevelRankingGenerator<LETTER, STATE, LevelRankingConstraintDrdCheck<LETTER, STATE>> {
	private static final boolean OMIT_NON_ACCEPTING_SINK = true;
	private final boolean mAllowEmptyLevelRanking;
	private final boolean mAllowRankZero;
	private final boolean mRestrictToElasticLevelRankings;
	private final boolean mVoluntaryDecreaseOnlyForStatesInO;
	private final boolean mAllowDelayedRankDecrease;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param userDefinedMaxRank
	 *            user-defined maximal rank
	 * @param allowRankZero
	 *            {@code true} iff rank zero is allowed
	 * @param allowEmptyLevelRanking
	 *            {@code true} iff empty level ranking is allowed
	 * @param restrictToElasticLevelRankings
	 *            {@code true} iff restriction to elastic level rankings is considered
	 * @param voluntaryDecreaseOnlyForStatesInO
	 *            TODO documentation
	 * @param allowDelayedRankDecrease
	 *            {@code true} iff delayed rank decrease is allowed
	 */
	public BarelyCoveredLevelRankingsGenerator(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final int userDefinedMaxRank,
			final boolean allowRankZero, final boolean allowEmptyLevelRanking,
			final boolean restrictToElasticLevelRankings, final boolean voluntaryDecreaseOnlyForStatesInO,
			final boolean allowDelayedRankDecrease) {
		super(services, operand, userDefinedMaxRank);
		mAllowRankZero = allowRankZero;
		mAllowEmptyLevelRanking = allowEmptyLevelRanking;
		mRestrictToElasticLevelRankings = restrictToElasticLevelRankings;
		mVoluntaryDecreaseOnlyForStatesInO = voluntaryDecreaseOnlyForStatesInO;
		mAllowDelayedRankDecrease = allowDelayedRankDecrease;
	}

	@Override
	public Collection<LevelRankingState<LETTER, STATE>> generateLevelRankings(
			final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final boolean predecessorIsSubsetComponent) {
		if (!mAllowEmptyLevelRanking && constraint.isEmpty()) {
			return Collections.emptyList();
		}
		if (constraint.isNonAcceptingSink()) {
			if (OMIT_NON_ACCEPTING_SINK) {
				return Collections.emptyList();
			}
			return Collections.singletonList(new LevelRankingState<LETTER, STATE>());
		}
		final List<LevelRankingState<LETTER, STATE>> succLvls = new ArrayList<>();
		final Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersEligibleForVoluntaryDecrease = new HashSet<>();
		for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : constraint.getPredecessorWasAccepting()) {
			if (complicatedCondition(constraint, doubleDecker)) {
				doubleDeckersEligibleForVoluntaryDecrease.add(doubleDecker);
			}
		}
		final Iterator<Set<DoubleDecker<StateWithRankInfo<STATE>>>> it =
				new PowersetIterator<>(doubleDeckersEligibleForVoluntaryDecrease);
		while (it.hasNext()) {
			final Set<DoubleDecker<StateWithRankInfo<STATE>>> subset = it.next();
			final LevelRankingState<LETTER, STATE> succCandidate = computeLevelRanking(constraint, subset);
			if ((succCandidate != null) && (!mRestrictToElasticLevelRankings || succCandidate.isElastic())) {
				succLvls.add(succCandidate);
			}
		}
		return succLvls;
	}

	private boolean complicatedCondition(final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker) {
			final boolean cond3 = condition3(constraint, doubleDecker);
			final boolean cond2 = condition2(constraint, doubleDecker);
			final boolean evenRankAndNotFinal = evenRankAndNotFinal(constraint, doubleDecker);
		return evenRankAndNotFinal(constraint, doubleDecker) && condition2(constraint, doubleDecker)
				&& condition3(constraint, doubleDecker);
	}

	private boolean evenRankAndNotFinal(final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker) {
		return LevelRankingState.isEven(constraint.getRank(doubleDecker.getDown(), doubleDecker.getUp().getState()))
				&& !mOperand.isFinal(doubleDecker.getUp().getState());
	}

	private boolean condition2(final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker) {
		return mAllowDelayedRankDecrease || constraint
				.nonAcceptingPredecessorsWithEvenRanksIsEmpty(doubleDecker.getDown(), doubleDecker.getUp().getState());
	}

	private boolean condition3(final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker) {
		return !mVoluntaryDecreaseOnlyForStatesInO
				|| constraint.inO(doubleDecker.getDown(), doubleDecker.getUp().getState());
	}

	private LevelRankingState<LETTER, STATE> computeLevelRanking(
			final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersWithVoluntaryDecrease) {
		final LevelRankingState<LETTER, STATE> result = new LevelRankingState<>(mOperand);
		for (final StateWithRankInfo<STATE> downState : constraint.getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : constraint.getUpStates(downState)) {
				final boolean oCandidate = upState.isInO();
				final int rankConstraint = upState.getRank();
				final Pair<Integer, Boolean> rankInOPair = getRankAndInO(doubleDeckersWithVoluntaryDecrease, downState,
						upState, oCandidate, rankConstraint);
				if (rankInOPair == null) {
					return null;
				}
				result.addRank(downState, upState.getState(), rankInOPair.getFirst(), rankInOPair.getSecond());
			}
		}
		return result;
	}

	private Pair<Integer, Boolean> getRankAndInO(
			final Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersWithVoluntaryDecrease,
			final StateWithRankInfo<STATE> downState, final StateWithRankInfo<STATE> upState, final boolean oCandidate,
			final int rankConstraint) {
		final boolean inO;
		final int rank;
		/*
		switch (rank) {
		case 3:
			if (mOperand.isFinal(up.getState())) {
				rank = 2;
				inO = oCandidate;
			} else {
				inO = false;
			}
			break;
		case 2:
			if (doubleDeckersWithVoluntaryDecrease.contains(
					new DoubleDecker<StateWithRankInfo<STATE>>(down, up))) {
				rank = 1;
				inO = false;
			} else {
				inO = oCandidate;
			}
			break;
		case 1:
			if (mOperand.isFinal(up.getState())) {
				return null;
			} else {
				inO = false;
			}
			break;
		default:
			throw new AssertionError("no other ranks allowed");
		}
		*/
		Pair<Integer, Boolean> rankInOPair;
		if (LevelRankingState.isOdd(rankConstraint)) {
			if (mOperand.isFinal(upState.getState())) {
				if (!mAllowRankZero && rankConstraint == 1) {
					return null;
				}
				rank = rankConstraint - 1;
				inO = oCandidate;
				rankInOPair = new Pair<>(rank, inO);
			} else {
				rank = rankConstraint;
				inO = false;
				rankInOPair = new Pair<>(rank, inO);
			}
		} else {
			assert LevelRankingState.isEven(rankConstraint);
			if (rankConstraint > 0
					&& doubleDeckersWithVoluntaryDecrease.contains(new DoubleDecker<>(downState, upState))) {
				rank = rankConstraint - 1;
				inO = false;
				rankInOPair = new Pair<>(rank, inO);
			} else {
				rank = rankConstraint;
				inO = oCandidate;
				rankInOPair = new Pair<>(rank, inO);
			}
		}
		return rankInOPair;
	}
}
