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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeRelation;

/**
 * Builder used by buchiComplementFKV to obtain TightLevelRankingStateGenerators.
 * <p>
 * TODO Christian 2016-08-16: FindBugs reports 7 problems in this class of the following form: The code uses x % 2 != 0
 * to check to see if a value is odd, but this won't work for negative numbers (e.g., (-5) % 2 == -1). If this code is
 * intending to check for oddness, consider using x & 1 == 1, or x % 2 != 0. TODO Christian 2016-08-19: Writes
 * <tt>"Sacrifice!"</tt> to logger on <tt>INFO</tt> level.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CONSTRAINT>
 *            constraint type
 */
public class MultiOptimizationLevelRankingGenerator<LETTER, STATE, CONSTRAINT extends LevelRankingConstraint<LETTER, STATE>>
		extends LevelRankingGenerator<LETTER, STATE, CONSTRAINT> {
	private final FkvOptimization mOptimization;

	/**
	 * Optimization options.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	public enum FkvOptimization {
		HEIMAT1,
		HEIMAT2,
		TIGHT_LEVEL_RANKINGS,
		HIGH_EVEN,
		SCHEWE,
		ELASTIC,
	}

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param optimization
	 *            optimization parameter
	 * @param userDefinedMaxRank
	 *            user-defined maximal rank
	 */
	public MultiOptimizationLevelRankingGenerator(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final FkvOptimization optimization,
			final int userDefinedMaxRank) {
		super(services, operand, userDefinedMaxRank);
		mOptimization = optimization;
	}

	@Override
	public Collection<LevelRankingState<LETTER, STATE>> generateLevelRankings(final CONSTRAINT constraint,
			final boolean predecessorIsSubsetComponent) {
		switch (mOptimization) {
			case HEIMAT1:
				return new HeiMatTightLevelRankingStateGenerator(constraint, false).computeResult();
			case HEIMAT2:
				return new HeiMatTightLevelRankingStateGenerator(constraint, true).computeResult();
			case HIGH_EVEN:
				return new HighEvenTightLevelRankingStateGenerator(constraint).computeResult();
			case SCHEWE:
				return generateLevelRankingsSchewe(constraint, predecessorIsSubsetComponent);
			case ELASTIC:
				return generateLevelRankingsElastic(constraint, predecessorIsSubsetComponent);
			case TIGHT_LEVEL_RANKINGS:
				return new TightLevelRankingStateGenerator(constraint).computeResult();
			default:
				throw new UnsupportedOperationException();
		}
	}

	private Collection<LevelRankingState<LETTER, STATE>> generateLevelRankingsSchewe(final CONSTRAINT constraint,
			final boolean predecessorIsSubsetComponent) {
		if (predecessorIsSubsetComponent) {
			return new MaxTightLevelRankingStateGeneratorInitial(constraint).computeResult();
		}
		return new MaxTightLevelRankingStateGeneratorNonInitial(constraint).computeResult();
	}

	private Collection<LevelRankingState<LETTER, STATE>> generateLevelRankingsElastic(final CONSTRAINT constraint,
			final boolean predecessorIsSubsetComponent) {
		if (predecessorIsSubsetComponent) {
			return new HeiMatTightLevelRankingStateGenerator(constraint, false).computeResult();
		}
		final boolean lazySOptimization = false;
		return new BarelyCoveredLevelRankingsGenerator<>(mServices, mOperand, mUserDefinedMaxRank, true, false, true,
				true, true, lazySOptimization).generateLevelRankings((LevelRankingConstraintDrdCheck<LETTER, STATE>) constraint, false);
	}

	/**
	 * Generates all LevelRanking states that are tight (see 2004ATVA paper) and fulfill given LevelRankingConstraints.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	class TightLevelRankingStateGenerator {
		protected int[] mUnrestrictedRank;

		protected final List<Integer> mRestrictedMaxRank = new ArrayList<>();
		protected int[] mRestrictedRank;

		protected final List<LevelRankingState<LETTER, STATE>> mResult = new ArrayList<>();
		protected final LevelRankingConstraint<LETTER, STATE> mConstraint;

		private final List<DoubleDecker<StateWithRankInfo<STATE>>> mUnrestrictedDoubleDeckerWithRankInfo =
				new ArrayList<>();
		private final List<Integer> mUnrestrictedMaxRank = new ArrayList<>();
		private final List<DoubleDecker<StateWithRankInfo<STATE>>> mRestrictedDoubleDeckerWithRankInfo =
				new ArrayList<>();

		public TightLevelRankingStateGenerator(final LevelRankingConstraint<LETTER, STATE> constraint) {
			mConstraint = constraint;
			partitionIntoRestrictedAndUnrestricted();
		}

		Collection<LevelRankingState<LETTER, STATE>> computeResult() {
			// mLogger.debug("Constructing LevelRankings for" + mUnrestrictedDoubleDeckerWithRankInfo.toString()
			//		+ mRestrictedDoubleDeckerWithRankInfo.toString());

			if (mUnrestrictedRank.length == 0 && mRestrictedRank.length == 0) {
				return Collections.emptySet();
			}

			initializeUnrestricted();
			boolean overflowUnrestricted;
			do {
				final int highestOddRank = getMaxNatOrZero(mUnrestrictedRank);
				if (highestOddRank % 2 != 0 && isOntoOddNatsUpToX(mUnrestrictedRank, highestOddRank)) {
					initializeRestricted(highestOddRank);
					boolean overflowRestricted;
					do {
						constructComplementState();
						overflowRestricted = increaseCounterRestricted(highestOddRank);
					} while (!overflowRestricted);
				}
				overflowUnrestricted = increaseCounterUnrestricted();
			} while (!overflowUnrestricted);
			return mResult;
		}

		/**
		 * Partition DoubleDeckerWithRankInfo into Restricted and Unrestricted. A double Decker is restricted iff is has
		 * to have an even rank in each LevelRankingState defined by this LevelRankingConstraint.
		 */
		private void partitionIntoRestrictedAndUnrestricted() {
			for (final StateWithRankInfo<STATE> downState : mConstraint.getDownStates()) {
				for (final StateWithRankInfo<STATE> upState : mConstraint.getUpStates(downState)) {
					final Integer rank = upState.getRank();
					if (mOperand.isFinal(upState.getState()) || rank == 0) {
						mRestrictedDoubleDeckerWithRankInfo.add(new DoubleDecker<>(downState, upState));
						mRestrictedMaxRank.add(rank);
					} else {
						mUnrestrictedDoubleDeckerWithRankInfo.add(new DoubleDecker<>(downState, upState));
						mUnrestrictedMaxRank.add(rank);
					}
				}
			}

			mUnrestrictedRank = new int[mUnrestrictedMaxRank.size()];
			mRestrictedRank = new int[mRestrictedMaxRank.size()];
		}

		private void constructComplementState() {
			// mLogger.debug("Rank " + Arrays.toString(mUnrestrictedRank) + Arrays.toString(mRestrictedRank));
			final LevelRankingState<LETTER, STATE> result = new LevelRankingState<>(mOperand);
			for (int i = 0; i < mRestrictedRank.length; i++) {
				final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker = mRestrictedDoubleDeckerWithRankInfo.get(i);
				final StateWithRankInfo<STATE> downState = doubleDecker.getDown();
				final StateWithRankInfo<STATE> upState = doubleDecker.getUp();
				final int rank = mRestrictedRank[i];
				final boolean addToO = mConstraint.inO(downState, upState.getState());
				result.addRank(downState, upState.getState(), rank, addToO);
			}

			for (int i = 0; i < mUnrestrictedRank.length; i++) {
				final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker =
						mUnrestrictedDoubleDeckerWithRankInfo.get(i);
				final StateWithRankInfo<STATE> downState = doubleDecker.getDown();
				final StateWithRankInfo<STATE> upState = doubleDecker.getUp();
				final int rank = mUnrestrictedRank[i];
				final boolean addToO = mConstraint.inO(downState, upState.getState()) && (rank % 2 == 0);
				result.addRank(downState, upState.getState(), rank, addToO);
			}
			mResult.add(result);
		}

		/**
		 * @return The maximal entry in given array, 0 if array is empty or maximum is < 0.
		 */
		private int getMaxNatOrZero(final int[] array) {
			int max = 0;
			for (int i = 0; i < array.length; i++) {
				if (array[i] > max) {
					max = array[i];
				}
			}
			return max;
		}

		/**
		 * @param array
		 *            of natural numbers
		 * @param an
		 *            odd number
		 * @return true iff every odd number from 1 up to x (including x) occurs in array.
		 */
		private boolean isOntoOddNatsUpToX(final int[] array, final int theX) {
			assert theX % 2 != 0;
			final int[] occurrence = new int[theX + 1];
			for (int i = 0; i < array.length; i++) {
				occurrence[array[i]]++;
			}
			for (int i = 1; i <= theX; i = i + 2) {
				if (occurrence[i] == 0) {
					return false;
				}
			}
			return true;
		}

		protected void initializeUnrestricted() {
			for (int i = 0; i < mUnrestrictedRank.length; i++) {
				mUnrestrictedRank[i] = 0;
			}
		}

		// TODO Christian 2016-09-08: The parameter 'highestOddRank' is never read - a bug?
		protected void initializeRestricted(final int highestOddRank) {
			for (int i = 0; i < mRestrictedRank.length; i++) {
				mRestrictedRank[i] = 0;
			}
		}

		/**
		 * @return true if overflow occured and therefore counter was reset or counter has length 0.
		 */
		private boolean increaseCounterUnrestricted() {
			if (mUnrestrictedRank.length == 0) {
				return true;
			}
			boolean overflow;
			int pos = 0;
			do {
				overflow = increaseDigitUnrestricted(pos);
				pos++;
			} while (overflow && pos < mUnrestrictedRank.length);
			return overflow;
		}

		protected boolean increaseDigitUnrestricted(final int pos) {
			final int oldDigit = mUnrestrictedRank[pos];
			final int newDigit = oldDigit + 1;
			assert maxTightRankUnrestricted(pos) >= 1;
			if (newDigit <= maxTightRankUnrestricted(pos)) {
				mUnrestrictedRank[pos] = newDigit;
				return false;
			}
			mUnrestrictedRank[pos] = 0;
			return true;
		}

		/**
		 * @return true if overflow occured and therefore counter was reset or counter has length 0.
		 */
		protected boolean increaseCounterRestricted(final int highestOddRank) {
			if (mRestrictedRank.length == 0) {
				return true;
			}
			boolean overflow;
			int pos = 0;
			do {
				overflow = increaseDigitRestricted(pos, highestOddRank);
				pos++;
			} while (overflow && pos < mRestrictedRank.length);
			return overflow;
		}

		private boolean increaseDigitRestricted(final int pos, final int highestOddRank) {
			final int oldDigit = mRestrictedRank[pos];
			final int newDigit = oldDigit + 2;
			if (newDigit <= maxTightRankRestricted(pos, highestOddRank)) {
				mRestrictedRank[pos] = newDigit;
				return false;
			}
			mRestrictedRank[pos] = 0;
			return true;
		}

		protected int maxTightRankUnrestricted(final int index) {
			final int numberOfStatesDefinedMaxRank = mUnrestrictedMaxRank.size() * 2 - 1;
			if (numberOfStatesDefinedMaxRank <= mUserDefinedMaxRank) {
				if (mUnrestrictedMaxRank.get(index) <= numberOfStatesDefinedMaxRank) {
					return mUnrestrictedMaxRank.get(index);
				}
				return numberOfStatesDefinedMaxRank;
			}
			if (mUnrestrictedMaxRank.get(index) <= mUserDefinedMaxRank) {
				return mUnrestrictedMaxRank.get(index);
			}
			return mUserDefinedMaxRank;
		}

		private int maxTightRankRestricted(final int index, final int highestOddRank) {
			if (highestOddRank <= mUserDefinedMaxRank) {
				if (mRestrictedMaxRank.get(index) <= highestOddRank) {
					return mRestrictedMaxRank.get(index);
				}
				return highestOddRank;
			}
			if (mRestrictedMaxRank.get(index) <= mUserDefinedMaxRank) {
				return mRestrictedMaxRank.get(index);
			}
			return mUserDefinedMaxRank;
		}
	}

	/**
	 * HeiMatTightLevelRankingStateGenerator.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class HeiMatTightLevelRankingStateGenerator extends TightLevelRankingStateGenerator {
		private static final int THOUSAND = 1000;
		private final TreeRelation<Integer, DoubleDecker<StateWithRankInfo<STATE>>> mUnrestrictedMaxRank2DoubleDeckerWithRankInfo;
		private final boolean mSuccessorsOfFinalsWantToLeaveO;
		//		private final int numberOfDoubleDeckerWithRankInfos;

		public HeiMatTightLevelRankingStateGenerator(final LevelRankingConstraint<LETTER, STATE> constraint,
				final boolean successorsOfFinalsWantToLeaveO) {
			super(constraint);
			mSuccessorsOfFinalsWantToLeaveO = successorsOfFinalsWantToLeaveO;
			mUnrestrictedMaxRank2DoubleDeckerWithRankInfo = new TreeRelation<>();
			// numberOfDoubleDeckerWithRankInfos =
			//		super.mUnrestrictedDoubleDeckerWithRankInfo.size();
			for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : super.mUnrestrictedDoubleDeckerWithRankInfo) {
				final Integer rank =
						constraint.mLevelRanking.get(doubleDecker.getDown()).get(doubleDecker.getUp().getState());
				mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.addPair(rank, doubleDecker);
			}
		}

		@Override
		Collection<LevelRankingState<LETTER, STATE>> computeResult() {
			final int unassignedUnrestricted = mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.size();
			if (unassignedUnrestricted == 0) {
				// all possible states are accepting or have rank 0
				// no state with odd rank possible, hence not tight - no successors
				return Collections.emptyList();
			}
			final LevelRankingWithSacrificeInformation lrwsi = new LevelRankingWithSacrificeInformation();
			final int assignedUnrestricted = 0;
			recursivelyComputeResults(0, lrwsi, assignedUnrestricted, unassignedUnrestricted);
			return mResult;
		}

		/**
		 * Returns all unrestricted DoubleDeckerWithRankInfos whose rank is rk.
		 */
		private DoubleDecker<StateWithRankInfo<STATE>>[] getUnrestrictedWithMaxRank(final int rank) {
			DoubleDecker<StateWithRankInfo<STATE>>[] result;
			@SuppressWarnings("unchecked")
			final DoubleDecker<StateWithRankInfo<STATE>>[] emptyDoubleDeckerWithRankInfoArray = new DoubleDecker[0];
			if (mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.getDomain().contains(rank)) {
				result = mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.getImage(rank)
						.toArray(emptyDoubleDeckerWithRankInfoArray);
			} else {
				result = emptyDoubleDeckerWithRankInfoArray;
			}
			return result;
		}

		/**
		 * Construct all stuffed levelRankings that are compatible with the partially constructed levelRanking lrwsi. In
		 * this iteration, we assign the (even) rank rk and the (odd) rank rk - 1.
		 * 
		 * @param rank
		 *            even rank such that all (odd?) ranks <tt>{@literal <} rk-2</tt> have already been assigned
		 * @param assignedUnrestricted
		 *            unrestricted DoubleDeckerWithRankInfos whose rank is already assigned
		 * @param unassignedUnrestricted
		 *            restricted DoubleDeckerWithRankInfos whose rank is not yet assigned
		 */
		private void recursivelyComputeResults(final int rank, final LevelRankingWithSacrificeInformation lrwsi,
				final int assignedUnrestricted, final int unassignedUnrestricted) {
			assert rank % 2 == 0;
			assert assignedUnrestricted + unassignedUnrestricted == super.mUnrestrictedDoubleDeckerWithRankInfo.size();

			final DoubleDecker<StateWithRankInfo<STATE>>[] constraintToRank = getUnrestrictedWithMaxRank(rank);
			if (unassignedUnrestricted == constraintToRank.length) {
				// the even ranks are already all unassigned (FIXME: don't understand this comment)
				// no chance for rk + 1
				// we have to give them the odd rk - 1
				// and finish afterwards
				lrwsi.addOddRanks(constraintToRank, rank - 1);
				addResult(lrwsi.assignRestrictedAndGetLevelRankingState());
				return;
			}

			if (lrwsi.numberUnsatisfiedLowerRanks() + 1 > unassignedUnrestricted) {
				throw new AssertionError("unable to assign all ranks");
			}

			/*
			 * Unrestricted DDs that we have to assign to rk + 1 because our
			 * constraints do not allow a higher rank.
			 */
			final DoubleDecker<StateWithRankInfo<STATE>>[] constraintToRankPlusOne =
					getUnrestrictedWithMaxRank(rank + 1);

			// List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO =
			//		new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
			/**
			 * States for which we definitely construct a copy in which they give up their even rank for the lower odd
			 * rank.
			 */
			final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantLeave = new ArrayList<>();
			/**
			 * States for which we only construct a copy in which their rank is reduced if this helps another state to
			 * obtain a high odd rank in a tight level ranking.
			 */
			final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantStay = new ArrayList<>();
			final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankNotInO = new ArrayList<>();
			for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : constraintToRank) {
				if (super.mConstraint.inO(doubleDecker.getDown(), doubleDecker.getUp().getState())) {
					if (mSuccessorsOfFinalsWantToLeaveO && !mOperand.isFinal(doubleDecker.getUp().getState())
							&& super.mConstraint.getPredecessorWasAccepting().contains(doubleDecker)) {
						constraintToRankInO_WantLeave.add(doubleDecker);
					} else {
						constraintToRankInO_WantStay.add(doubleDecker);
					}
					//					constraintToRankInO.add(dd);
				} else {
					constraintToRankNotInO.add(doubleDecker);
				}

			}

			// number of copies that we need in this iteration
			final int numberOfCopies;
			if (rank > 0) {
				numberOfCopies = (int) Math.pow(2, constraintToRank.length);
			} else {
				numberOfCopies = 1;
			}

			/* Example: Assume we have not yet assigned any rank and the maximal
			 * ranks are (5 4 4 2). The level ranking (5 4 4 2) is not stuffed,
			 * because rank 1 and rank 3 are not satisfied. But the following
			 * five level rankings are a maximal set of level rankings that
			 * fulfill the constraints.
			 * (5 3 3 2) (5 3 1 2) (5 1 3 2) (5 4 3 1) (5 3 4 1)
			 * We want to construct them. Therefore we have to give some
			 * candidates for the even rank rk, the odd rank rk - 1 instead.
			 * E.g., two DoubleDeckerWithRankInfos in this example.
			 */

			// number of odd ranks that we have to assign with even-candidates
			// in order to be able to assign the odd rank rk + 1
			final int numberOfOddRanksThatWeHaveToAssignAdditionally =
					lrwsi.numberUnsatisfiedLowerRanks() + 1 - (unassignedUnrestricted - constraintToRank.length);
			final int unassignedUnrestrictedAfterThisTurn =
					unassignedUnrestricted - constraintToRank.length - constraintToRankPlusOne.length;
			final int assignedUnrestrictedAfterThisTurn =
					assignedUnrestricted + constraintToRank.length + constraintToRankPlusOne.length;

			int surplus = surplus(rank);
			surplus = surplus(rank);
			final int maxNumberOfEvenRanksWeMayAssign =
					unassignedUnrestricted - (lrwsi.numberUnsatisfiedLowerRanks() + 1);
			final int surplusRk = surplus(rank);
			final int netSurplus = surplusRk - lrwsi.numberUnsatisfiedLowerRanks();
			final int numberOfOddRankTheWeCouldAssignAdditionally =
					Math.max(lrwsi.numberUnsatisfiedLowerRanks() - surplusRk, 0);
			if (numberOfOddRankTheWeCouldAssignAdditionally > 1 && numberOfCopies > 1) {
				mLogger.info("Sacrifice!");
			}

			// assert constraintToRank.length - maxNumberOfEvenRanksWeMayAssign
			//		== numberOfOddRanksThatWeHaveToAssignAdditionally;

			final int inO_leavemultiplier = (int) Math.pow(2, constraintToRankInO_WantLeave.size());
			final int inO_staymultiplier = (int) Math.pow(2, constraintToRankInO_WantStay.size());

			//			int inOmultiplier = (int) Math.pow(2, constraintToRankInO.size());
			final int notInOmultiplier = (int) Math.pow(2, constraintToRankNotInO.size());
			//			assert (numberOfCopies == inOmultiplier * notInOmultiplier);
			assert numberOfCopies == inO_leavemultiplier * inO_staymultiplier * notInOmultiplier;

			outerLoop(rank, lrwsi, constraintToRankPlusOne, constraintToRankInO_WantLeave, constraintToRankInO_WantStay,
					constraintToRankNotInO, numberOfOddRanksThatWeHaveToAssignAdditionally,
					unassignedUnrestrictedAfterThisTurn, assignedUnrestrictedAfterThisTurn,
					maxNumberOfEvenRanksWeMayAssign, numberOfOddRankTheWeCouldAssignAdditionally, inO_leavemultiplier,
					inO_staymultiplier, notInOmultiplier);
		}

		private void outerLoop(final Integer rank, final LevelRankingWithSacrificeInformation lrwsi,
				final DoubleDecker<StateWithRankInfo<STATE>>[] constraintToRankPlusOne,
				final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantLeave,
				final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantStay,
				final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankNotInO,
				final int numberOfOddRanksThatWeHaveToAssignAdditionally, final int unassignedUnrestrictedAfterThisTurn,
				final int assignedUnrestrictedAfterThisTurn, final int maxNumberOfEvenRanksWeMayAssign,
				final int numberOfOddRankTheWeCouldAssignAdditionally, final int inO_leavemultiplier,
				final int inO_staymultiplier, final int notInOmultiplier) {
			for (int iol = 0; iol < inO_leavemultiplier; iol++) {
				final int bitcountIol = Integer.bitCount(iol);
				if (bitcountIol + constraintToRankNotInO.size() < numberOfOddRanksThatWeHaveToAssignAdditionally) {
					// we give up this branch, we can not achieve that each
					// odd rank is assigned once.
					continue;
				}
				for (int ios = 0; ios < inO_staymultiplier; ios++) {
					final int bitcountI = Integer.bitCount(ios);
					if (bitcountIol + bitcountI
							+ constraintToRankNotInO.size() < numberOfOddRanksThatWeHaveToAssignAdditionally) {
						// we give up this branch, we can not achieve that each
						// odd rank is assigned once.
						continue;
					}
					innerLoop(rank, lrwsi, constraintToRankPlusOne, constraintToRankInO_WantLeave,
							constraintToRankInO_WantStay, constraintToRankNotInO,
							numberOfOddRanksThatWeHaveToAssignAdditionally, unassignedUnrestrictedAfterThisTurn,
							assignedUnrestrictedAfterThisTurn, maxNumberOfEvenRanksWeMayAssign,
							numberOfOddRankTheWeCouldAssignAdditionally, notInOmultiplier, iol, bitcountIol, ios,
							bitcountI);
				}
			}
		}

		private void innerLoop(final int rank, final LevelRankingWithSacrificeInformation lrwsi,
				final DoubleDecker<StateWithRankInfo<STATE>>[] constraintToRankPlusOne,
				final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantLeave,
				final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantStay,
				final List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankNotInO,
				final int numberOfOddRanksThatWeHaveToAssignAdditionally, final int unassignedUnrestrictedAfterThisTurn,
				final int assignedUnrestrictedAfterThisTurn, final int maxNumberOfEvenRanksWeMayAssign,
				final int numberOfOddRankTheWeCouldAssignAdditionally, final int notInOmultiplier, final int iol,
				final int bitcountIol, final int ios, final int bitcountI) {
			for (int j = 0; j < notInOmultiplier; j++) {
				final int bitcountJ = Integer.bitCount(j);
				if (bitcountIol + bitcountI + bitcountJ < numberOfOddRanksThatWeHaveToAssignAdditionally) {
					// we give up this branch, we can not achieve that each
					// odd rank is assigned once.
					continue;
				}
				if ((bitcountI > 0 || bitcountJ > 0)
						// in the special case that both bitcount_ios and
						// bitcount nio are zero we do not give up this
						// branch. The rank decrease is not a sacrifice,
						// the rank decrease is done because the state
						// wants to leave O in one copy.
						&& (bitcountIol + bitcountI + bitcountJ > numberOfOddRankTheWeCouldAssignAdditionally)) {
					// we give up this branch, sacrificing that many even
					// ranks wont' bring us a higher maximal rank
					continue;
				}
				final LevelRankingWithSacrificeInformation copy = new LevelRankingWithSacrificeInformation(lrwsi);
				for (int k = 0; k < constraintToRankInO_WantLeave.size(); k++) {
					if (BigInteger.valueOf(iol).testBit(k)) {
						copy.addOddRank(constraintToRankInO_WantLeave.get(k), rank - 1, true);
					}
				}
				for (int k = 0; k < constraintToRankInO_WantStay.size(); k++) {
					if (BigInteger.valueOf(ios).testBit(k)) {
						copy.addOddRank(constraintToRankInO_WantStay.get(k), rank - 1, true);
					}
				}
				for (int k = 0; k < constraintToRankNotInO.size(); k++) {
					if (BigInteger.valueOf(j).testBit(k)) {
						copy.addOddRank(constraintToRankNotInO.get(k), rank - 1, true);
					}
				}
				copy.increaseCurrentRank();
				assert copy.mCurrentRank == rank;
				int evenRanksAssignedSoFar = 0;
				for (int k = 0; k < constraintToRankInO_WantLeave.size(); k++) {
					if (!BigInteger.valueOf(iol).testBit(k)) {
						copy.addEvenRank(constraintToRankInO_WantLeave.get(k), rank);
						evenRanksAssignedSoFar++;
					}
				}
				for (int k = 0; k < constraintToRankInO_WantStay.size(); k++) {
					if (!BigInteger.valueOf(ios).testBit(k)) {
						copy.addEvenRank(constraintToRankInO_WantStay.get(k), rank);
						evenRanksAssignedSoFar++;
					}
				}
				for (int k = 0; k < constraintToRankNotInO.size(); k++) {
					if (!BigInteger.valueOf(j).testBit(k)) {
						copy.addEvenRank(constraintToRankNotInO.get(k), rank);
						evenRanksAssignedSoFar++;
					}
				}
				assert evenRanksAssignedSoFar <= maxNumberOfEvenRanksWeMayAssign;
				copy.increaseCurrentRank();
				copy.addOddRanks(constraintToRankPlusOne, rank + 1);
				final int numberUnassignedLowerRanks = copy.numberUnsatisfiedLowerRanks();
				if (unassignedUnrestrictedAfterThisTurn == numberUnassignedLowerRanks) {
					copy.assignRemainingUnrestricted(rank + 1, unassignedUnrestrictedAfterThisTurn);
					addResult(copy.assignRestrictedAndGetLevelRankingState());
					continue;
				}
				recursivelyComputeResults(rank + 2, copy, assignedUnrestrictedAfterThisTurn,
						unassignedUnrestrictedAfterThisTurn);
				continue;
			}
		}

		/**
		 * If we assign ranks starting from the highest down to i such that we given even ranks for even bounds, how
		 * many ranks do we have as surplus that we can use to satisfy odd ranks < i without having
		 * DoubleDeckerWithRankInfos for this rank. E.g., for the ranks 5 3 1, the surplus for i = 3 is 0 for the ranks
		 * 3 3 1, the surplus for i = 3 is 1 for the ranks 3 2 1, the surplus for i = 3 is 0 for the ranks 4 3 1, the
		 * surplus for i = 3 is 1 for the ranks ∞ ∞ 3, the surplus for i = 3 is 0 for the ranks ∞ ∞ 3, 3 the surplus for
		 * i = 3 is 1 for the ranks ∞ ∞ 4, 3 the surplus for i = 3 is 0 for the ranks 11 9 5 5 3 the surplus for i = 3
		 * is 1
		 */
		private int surplus(final int i) {
			final int highestBound;
			{
				final Iterator<Integer> it =
						mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.descendingDomain().iterator();
				assert it.hasNext();
				final int first = it.next();
				if (first == Integer.MAX_VALUE) {
					if (it.hasNext()) {
						highestBound = it.next();
					} else {
						// no surplus, all have rank = ∞ = Integer.MAX_VALUE
						return 0;
					}
				} else {
					highestBound = first;
				}
			}
			final int unbounded = mUnrestrictedMaxRank2DoubleDeckerWithRankInfo
					.numberofPairsWithGivenDomainElement(Integer.MAX_VALUE);
			int rank;
			int surplus;
			if (LevelRankingState.isEven(highestBound)) {
				// if rank is even
				// if there some with ∞-bound these even rank do not contribute
				// to the surplus
				// if there no with ∞-bound all these have to take the next odd
				// rank
				if (unbounded > 0) {
					surplus = 0;
				} else {
					surplus = mUnrestrictedMaxRank2DoubleDeckerWithRankInfo
							.numberofPairsWithGivenDomainElement(highestBound);
				}
				rank = highestBound - 1;
			} else {
				surplus = 0;
				rank = highestBound;
			}
			while (rank >= i) {
				assert LevelRankingState.isOdd(rank);
				final int ddWithRank =
						mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.numberofPairsWithGivenDomainElement(rank);
				surplus += (ddWithRank - 1);
				if (surplus < 0) {
					assert surplus == -1;
					surplus = 0;
				}
				rank -= 2;
			}
			return surplus;
		}

		private void addResult(final LevelRankingState<LETTER, STATE> lrs) {
			assert lrs.mLevelRanking.size() == super.mConstraint.mLevelRanking.size();
			mResult.add(lrs);
		}

		@Override
		public String toString() {
			return super.mConstraint.toString() + " Unrestricted: " + super.mUnrestrictedDoubleDeckerWithRankInfo;
		}

		void assignRemainingUnrestricted(final int rank, final LevelRankingState<LETTER, STATE> lrs,
				final int unassignedUnrestrictedIn) {
			int unassignedUnrestricted = unassignedUnrestrictedIn;
			assert rank % 2 != 0 : "maxrank is always odd";
			final Integer noRankBound = Integer.MAX_VALUE;
			if (mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.getDomain().contains(noRankBound)) {
				for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : mUnrestrictedMaxRank2DoubleDeckerWithRankInfo
						.getImage(noRankBound)) {
					lrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), rank, false);
					unassignedUnrestricted--;
				}
			}
			assert unassignedUnrestricted >= 0;
			int rankBound = rank + 1;
			while (unassignedUnrestricted > 0) {
				if (mUnrestrictedMaxRank2DoubleDeckerWithRankInfo.getDomain().contains(rankBound)) {
					for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : mUnrestrictedMaxRank2DoubleDeckerWithRankInfo
							.getImage(rankBound)) {
						lrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), rank, false);
						unassignedUnrestricted--;
					}
				}
				rankBound++;
				if (rankBound > THOUSAND) {
					throw new AssertionError(
							"forgotten rank bound?, there are no automata with rank > " + THOUSAND + " in the nature");
				}
			}
		}

		/**
		 * LevelRankingWithSacrificeInformation.
		 * 
		 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
		 */
		private class LevelRankingWithSacrificeInformation {
			private final LevelRankingState<LETTER, STATE> mLrs;
			private int mCurrentRank = -1;
			/**
			 * Number of odd ranks rk such that the number of DoubleDeckerWithRankInfos that have an odd rank i >= rk is
			 * smaller than or equal to (mCurrentRank - rk + 1).
			 */
			private final TreeSet<Integer> mUnSatisfiedOddRanks;
			//			private final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> mSacrificable;
			/**
			 * DoubleDeckerWithRankInfos that we assigned the odd rank rk although its constraints would have allows the
			 * even rank rk + 1.
			 */
			private final List<DoubleDecker<StateWithRankInfo<STATE>>> mSacrificedDoubleDeckerWithRankInfos;

			public LevelRankingWithSacrificeInformation(final LevelRankingWithSacrificeInformation copy) {
				this.mLrs = new LevelRankingState<>(copy.mLrs);
				mCurrentRank = copy.mCurrentRank;
				mUnSatisfiedOddRanks = new TreeSet<>(copy.mUnSatisfiedOddRanks);
				mSacrificedDoubleDeckerWithRankInfos = new ArrayList<>(copy.mSacrificedDoubleDeckerWithRankInfos);
				// mSacrificable = new HashMap<DoubleDecker<StateWithRankInfo<STATE>>, Integer>(copy.mSacrificable);
			}

			LevelRankingWithSacrificeInformation() {
				mLrs = new LevelRankingState<>(mOperand);
				mUnSatisfiedOddRanks = new TreeSet<>();
				mSacrificedDoubleDeckerWithRankInfos = new ArrayList<>();
				// mSacrificable = new HashMap<DoubleDecker<StateWithRankInfo<STATE>>, Integer>();
			}

			int numberUnsatisfiedLowerRanks() {
				return mUnSatisfiedOddRanks.size();
			}

			void increaseCurrentRank() {
				mCurrentRank++;
				if (mCurrentRank % 2 != 0) {
					mUnSatisfiedOddRanks.add(mCurrentRank);
				}
			}

			void addOddRank(final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker, final int rank,
					final boolean isSacrifice) {
				assert rank % 2 != 0;
				assert rank == mCurrentRank;
				final boolean addToO = false;
				mLrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), rank, addToO);
				final Integer removed = mUnSatisfiedOddRanks.pollLast();
				if (isSacrifice) {
					mSacrificedDoubleDeckerWithRankInfos.add(doubleDecker);
				}
				//				if (removed != null) {
				//					updateSacrificable(removed);
				//				}
			}

			void addOddRanks(final DoubleDecker<StateWithRankInfo<STATE>>[] dds, final int rank) {
				for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : dds) {
					addOddRank(doubleDecker, rank, false);
				}
			}

			/*
			private void updateSacrificable(Integer removed) {
				Iterator<Entry<DoubleDecker<StateWithRankInfo<STATE>>, Integer>> it =
						mSacrificable.entrySet().iterator();
				while (it.hasNext()) {
					Entry<DoubleDecker<StateWithRankInfo<STATE>>, Integer> entry = it.next();
					if (entry.getValue().equals(removed)) {
						Integer nextHighest = mUnassignedOddRanks.floor(removed);
						if (nextHighest == null) {
							it.remove();
						} else {
							entry.setValue(nextHighest);
						}
					}
				}
			}
			*/

			void addEvenRank(final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker, final int rank) {
				assert rank % 2 == 0;
				assert rank == mCurrentRank;
				final boolean addToO = HeiMatTightLevelRankingStateGenerator.super.mConstraint
						.inO(doubleDecker.getDown(), doubleDecker.getUp().getState());
				mLrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), rank, addToO);
				if (!mUnSatisfiedOddRanks.isEmpty()) {
					final Integer highestUnassigned = mUnSatisfiedOddRanks.last();
					assert highestUnassigned < rank;
					// mSacrificable.put(dd, highestUnassigned);
				}
			}

			/**
			 * @return The level ranking state which was restricted.
			 */
			public LevelRankingState<LETTER, STATE> assignRestrictedAndGetLevelRankingState() {
				if (!mUnSatisfiedOddRanks.isEmpty()) {
					throw new AssertionError("not all odd ranks assigned yet");
				}
				assert mLrs.mHighestRank % 2 != 0 : "maxrank is always odd";
				for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : HeiMatTightLevelRankingStateGenerator.super.mRestrictedDoubleDeckerWithRankInfo) {
					Integer rank;
					final boolean inO = HeiMatTightLevelRankingStateGenerator.super.mConstraint
							.inO(doubleDecker.getDown(), doubleDecker.getUp().getState());
					if (HeiMatTightLevelRankingStateGenerator.super.mConstraint.getRank(doubleDecker.getDown(),
							doubleDecker.getUp().getState()) <= mLrs.mHighestRank) {
						final int bound = HeiMatTightLevelRankingStateGenerator.super.mConstraint
								.getRank(doubleDecker.getDown(), doubleDecker.getUp().getState());
						if (bound % 2 == 0) {
							rank = bound;
						} else {
							rank = bound - 1;
						}
					} else {
						if (mSacrificedDoubleDeckerWithRankInfos.size() > 1) {
							// 2016-02-05 Matthias: I checked this on the Michael4 example
							// and could not see obvious problem.
							// Maybe this is new because we decrease the rank after visiting a final state.
							mLogger.warn("unneccessary sacrifice !!! this state is is not needed, "
									+ "construction can be optimized, contact Matthias");
						}
						rank = mLrs.mHighestRank - 1;
					}
					mLrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), rank, inO);
				}
				return mLrs;
			}

			void assignRemainingUnrestricted(final Integer rank, final int unassignedUnrestricted) {
				assert rank == mCurrentRank;
				assert unassignedUnrestricted >= mUnSatisfiedOddRanks.size();
				HeiMatTightLevelRankingStateGenerator.this.assignRemainingUnrestricted(rank, mLrs,
						unassignedUnrestricted);
				mUnSatisfiedOddRanks.clear();
			}
		}
	}

	/**
	 * Generates all LevelRanking states that are tight (see 2004ATVA paper), fulfill given LevelRankingConstraints and
	 * fulfill the following property: If a DoubleDeckerWithRankInfo has an even rank it must the the highest possible
	 * even rank. Warning: I think a restriction to LevelRanking that satisfy also the latter property leads to a sound
	 * complementation, but it is not mentioned in any paper and I do not have a proof for that.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class HighEvenTightLevelRankingStateGenerator extends TightLevelRankingStateGenerator {
		public HighEvenTightLevelRankingStateGenerator(final LevelRankingConstraint<LETTER, STATE> constraints) {
			super(constraints);
		}

		@Override
		protected void initializeRestricted(final int highestOddRank) {
			if (highestOddRank == 0) {
				for (int i = 0; i < mRestrictedRank.length; i++) {
					mRestrictedRank[i] = 0;
				}
				return;
			}
			assert highestOddRank > 0 && highestOddRank % 2 != 0;
			for (int i = 0; i < mRestrictedRank.length; i++) {
				if (highestOddRank < mRestrictedMaxRank.get(i)) {
					mRestrictedRank[i] = highestOddRank - 1;
				} else if (mRestrictedMaxRank.get(i) % 2 != 0) {
					mRestrictedRank[i] = mRestrictedMaxRank.get(i) - 1;
				} else {
					mRestrictedRank[i] = mRestrictedMaxRank.get(i);
				}
			}
		}

		@Override
		protected boolean increaseDigitUnrestricted(final int pos) {
			final int oldDigit = mUnrestrictedRank[pos];
			if (oldDigit == maxTightRankUnrestricted(pos)) {
				mUnrestrictedRank[pos] = 1;
				return true;
			}
			int newDigit;
			assert maxTightRankUnrestricted(pos) >= 1;
			if (oldDigit + 2 <= maxTightRankUnrestricted(pos)) {
				newDigit = oldDigit + 2;
			} else {
				newDigit = oldDigit + 1;
				assert newDigit == maxTightRankUnrestricted(pos);
				assert newDigit % 2 == 0;
			}
			mUnrestrictedRank[pos] = newDigit;
			return false;
		}

		@Override
		protected boolean increaseCounterRestricted(final int highestOddRank) {
			return true;
		}

		@Override
		protected void initializeUnrestricted() {
			for (int i = 0; i < mUnrestrictedRank.length; i++) {
				mUnrestrictedRank[i] = 1;
			}
		}
	}

	/**
	 * Use this together with MaxTightLevelRankingStateGeneratorNonInitial. The
	 * MaxTightLevelRankingStateGeneratorInitial should generate the LevelRankings for successors of determinized states
	 * (from powerset construction) the MaxTightLevelRankingStateGeneratorNonInitial should generate other
	 * LevelRankings. I tried to implement the optimization suggested in Section 4 of 2009STACS - Schewe - Büchi
	 * Complementation Made Tight This is still buggy and meanwhile I think that my optimization is more efficient.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class MaxTightLevelRankingStateGeneratorInitial extends TightLevelRankingStateGenerator {
		private final List<DoubleDecker<StateWithRankInfo<STATE>>> mFinalDoubleDeckerWithRankInfos = new ArrayList<>();
		private final List<DoubleDecker<StateWithRankInfo<STATE>>> mNonFinalDoubleDeckerWithRankInfos =
				new ArrayList<>();

		public MaxTightLevelRankingStateGeneratorInitial(final LevelRankingConstraint<LETTER, STATE> constraint) {
			super(constraint);
			for (final StateWithRankInfo<STATE> downState : constraint.getDownStates()) {
				for (final StateWithRankInfo<STATE> upState : constraint.getUpStates(downState)) {
					assert upState.getRank() == mUserDefinedMaxRank;
					final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker = new DoubleDecker<>(downState, upState);
					if (mOperand.isFinal(upState.getState())) {
						mFinalDoubleDeckerWithRankInfos.add(doubleDecker);
					} else {
						mNonFinalDoubleDeckerWithRankInfos.add(doubleDecker);
					}
				}
			}

		}

		public void rec(final int rank, final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assigned) {
			if (assigned.size() == mNonFinalDoubleDeckerWithRankInfos.size()) {
				final int maxrank = rank - 2;
				final LevelRankingState<LETTER, STATE> lrs = constructLevelRankingState(assigned, maxrank);
				mResult.add(lrs);
			} else {
				for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : mNonFinalDoubleDeckerWithRankInfos) {
					if (!assigned.containsKey(doubleDecker)) {
						final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assignedCopy =
								new HashMap<>(assigned);
						assignedCopy.put(doubleDecker, rank);
						rec(rank + 2, assignedCopy);
					}
				}
				addLevelRankingState(rank, assigned);
			}
		}

		private void addLevelRankingState(final int rank,
				final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assigned) {
			// construct copy where maxrank is the current rank
			final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assignedCopy = new HashMap<>(assigned);
			for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : mNonFinalDoubleDeckerWithRankInfos) {
				if (!assignedCopy.containsKey(doubleDecker)) {
					assignedCopy.put(doubleDecker, rank);
				}
			}
			final int maxrank = rank;
			final LevelRankingState<LETTER, STATE> lrs = constructLevelRankingState(assignedCopy, maxrank);
			mResult.add(lrs);
		}

		private LevelRankingState<LETTER, STATE> constructLevelRankingState(
				final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assigned, final int maxrank) {
			assert assigned.size() == mNonFinalDoubleDeckerWithRankInfos.size() : "not ready for construction";
			final int highestEvenRank = maxrank - 1;
			final LevelRankingState<LETTER, STATE> lrs = new LevelRankingState<>(mOperand);
			for (final Entry<DoubleDecker<StateWithRankInfo<STATE>>, Integer> entry : assigned.entrySet()) {
				final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker = entry.getKey();
				lrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), entry.getValue(), false);
			}
			for (final DoubleDecker<StateWithRankInfo<STATE>> doubleDecker : mFinalDoubleDeckerWithRankInfos) {
				lrs.addRank(doubleDecker.getDown(), doubleDecker.getUp().getState(), highestEvenRank, true);
			}
			assert lrs.isMaximallyTight() : "not maximally tight";
			return lrs;
		}

		@Override
		Collection<LevelRankingState<LETTER, STATE>> computeResult() {
			if (!mNonFinalDoubleDeckerWithRankInfos.isEmpty()) {
				final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> empty = Collections.emptyMap();
				rec(1, empty);
			}
			return mResult;
		}

	}

	/**
	 * Use this together with MaxTightLevelRankingStateGeneratorInitial.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class MaxTightLevelRankingStateGeneratorNonInitial extends TightLevelRankingStateGenerator {
		public MaxTightLevelRankingStateGeneratorNonInitial(final LevelRankingConstraint<LETTER, STATE> constraint) {
			super(constraint);
		}

		@Override
		Collection<LevelRankingState<LETTER, STATE>> computeResult() {
			if (mConstraint.getDownStates().isEmpty()) {
				return Collections.emptySet();
			}
			if (!mConstraint.isTight()) {
				return mResult;
			}
			final LevelRankingState<LETTER, STATE> pointwiseMax = new LevelRankingState<>(mOperand);
			for (final StateWithRankInfo<STATE> downState : mConstraint.getDownStates()) {
				for (final StateWithRankInfo<STATE> upState : mConstraint.getUpStates(downState)) {
					int rank = upState.getRank();
					if (mOperand.isFinal(upState.getState()) && LevelRankingState.isOdd(rank)) {
						rank--;
					}
					if (upState.isInO() && LevelRankingState.isEven(rank)) {
						pointwiseMax.addRank(downState, upState.getState(), rank, true);
					} else {
						pointwiseMax.addRank(downState, upState.getState(), rank, false);
					}
				}
			}
			if (pointwiseMax.isTight()) {
				mResult.add(pointwiseMax);
			} else {
				assert mResult.isEmpty();
				return mResult;
			}
			computeResultHelper(pointwiseMax);
			return mResult;
		}

		private void computeResultHelper(final LevelRankingState<LETTER, STATE> pointwiseMax) {
			if (pointwiseMax.isOempty()) {
				return;
			}
			final LevelRankingState<LETTER, STATE> lrs = new LevelRankingState<>(mOperand);
			for (final StateWithRankInfo<STATE> downState : pointwiseMax.getDownStates()) {
				for (final StateWithRankInfo<STATE> upState : pointwiseMax.getUpStates(downState)) {
					final int rank = upState.getRank();
					if (!upState.isInO()) {
						lrs.addRank(downState, upState.getState(), rank, false);
					} else if (rank == 0 || mOperand.isFinal(upState.getState())) {
						lrs.addRank(downState, upState.getState(), rank, true);
					} else {
						lrs.addRank(downState, upState.getState(), rank - 1, false);
					}
				}
			}
			if (!lrs.equals(pointwiseMax)) {
				mResult.add(lrs);
			}
		}
	}
}
