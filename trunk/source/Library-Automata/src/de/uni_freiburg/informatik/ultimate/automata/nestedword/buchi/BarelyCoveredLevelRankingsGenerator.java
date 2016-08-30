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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.util.datastructures.PowersetIterator;

public class BarelyCoveredLevelRankingsGenerator<LETTER, STATE>
		extends LevelRankingGenerator<LETTER, STATE, LevelRankingConstraintDrdCheck<LETTER, STATE>> {
	
	private final boolean mOmitNonAcceptingSink = true;
	private final boolean mAllowEmptyLevelRanking;
	private final boolean mAllowRankZero;
	private final boolean mRestrictToElasticLevelRankings;
	private final boolean mVoluntaryDecreaseOnlyForStatesInO;
	private final boolean mAllowDelayedRankDecrease;

	public BarelyCoveredLevelRankingsGenerator(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand, final int userDefinedMaxRank,
			final boolean allowRankZero,
			final boolean allowEmptyLevelRanking,
			final boolean restrictToElasticLevelRankings,
			final boolean voluntaryDecreaseOnlyForStatesInO,
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
			if (mOmitNonAcceptingSink ) {
				return Collections.emptyList();
			} else {
				return Collections.singletonList(new LevelRankingState<LETTER, STATE>());
			}
		}
		final List<LevelRankingState<LETTER, STATE>> succLvls = new ArrayList<LevelRankingState<LETTER,STATE>>();
		final Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersEligibleForVoluntaryDecrease = new HashSet<>();
		for (final DoubleDecker<StateWithRankInfo<STATE>> dd : constraint.getPredecessorWasAccepting()) {
			if (LevelRankingState.isEven(constraint.getRank(dd.getDown(), dd.getUp().getState()))
					&& !mOperand.isFinal(dd.getUp().getState())) {
				if (mAllowDelayedRankDecrease || constraint.nonAcceptingPredecessorsWithEvenRanksIsEmpty(
						dd.getDown(), dd.getUp().getState())) {
					if (!mVoluntaryDecreaseOnlyForStatesInO || constraint.inO(dd.getDown(), dd.getUp().getState())) {
						doubleDeckersEligibleForVoluntaryDecrease.add(dd);
					}
				}
			}
			
		}
		final Iterator<Set<DoubleDecker<StateWithRankInfo<STATE>>>> it =
				new PowersetIterator<DoubleDecker<StateWithRankInfo<STATE>>>(doubleDeckersEligibleForVoluntaryDecrease);
		while (it.hasNext()) {
			final Set<DoubleDecker<StateWithRankInfo<STATE>>> subset = it.next();
			final LevelRankingState<LETTER, STATE> succCandidate = computeLevelRanking(constraint, subset);
			if (succCandidate != null) {
				if (!mRestrictToElasticLevelRankings || succCandidate.isElastic()) {
					succLvls.add(succCandidate);
				}
			}
		}
		return succLvls;
	}
	
	
	private LevelRankingState<LETTER, STATE> computeLevelRanking(
			final LevelRankingConstraintDrdCheck<LETTER, STATE> constraint,
			final Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersWithVoluntaryDecrease) {
		final LevelRankingState<LETTER, STATE> result = new LevelRankingState<LETTER, STATE>(mOperand);
		for (final StateWithRankInfo<STATE> down : constraint.getDownStates()) {
			for (final StateWithRankInfo<STATE> up : constraint.getUpStates(down)) {
				final boolean oCandidate = up.isInO();
				final int rankConstraint = up.getRank();
				final boolean inO;
				final int rank;
//				switch (rank) {
//				case 3:
//					if (mOperand.isFinal(up.getState())) {
//						rank = 2;
//						inO = oCandidate;
//					} else {
//						inO = false;
//					}
//					break;
//				case 2:
//					if (doubleDeckersWithVoluntaryDecrease.contains(
//							new DoubleDecker<StateWithRankInfo<STATE>>(down, up))) {
//						rank = 1;
//						inO = false;
//					} else {
//						inO = oCandidate;
//					}
//					break;
//				case 1:
//					if (mOperand.isFinal(up.getState())) {
//						return null;
//					} else {
//						inO = false;
//					}
//					break;
//				default:
//					throw new AssertionError("no other ranks allowed");
//				}
				if (LevelRankingState.isOdd(rankConstraint)) {
					if (mOperand.isFinal(up.getState())) {
						if (!mAllowRankZero && rankConstraint == 1) {
							return null;
						} else {
							rank = rankConstraint - 1;
							inO = oCandidate;
						}
					} else {
						rank = rankConstraint;
						inO = false;
					}
				} else {
					assert LevelRankingState.isEven(rankConstraint);
					if (rankConstraint > 0
							&& doubleDeckersWithVoluntaryDecrease.contains(
									new DoubleDecker<StateWithRankInfo<STATE>>(down, up))) {
						rank = rankConstraint - 1;
						inO = false;
					} else {
						rank = rankConstraint;
						inO = oCandidate;
					}
				}
				result.addRank(down, up.getState(), rank, inO);
			}
		}
		return result;
	}

}
