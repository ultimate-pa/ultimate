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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates.InCaRe;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Class for obtaining NestedLassoRun which are accepted by a
 * NestedWordAutomatonReachableStates.
 * <p>
 * This class is buggy, old and superseded by the class LassoConstructor.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
class LassoExtractor<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mNwars;
	
	private final NestedLassoRun<LETTER, STATE> mNlr;
	
	public LassoExtractor(final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> nwars,
			final StateContainer<LETTER, STATE> honda,
			final StronglyConnectedComponent<StateContainer<LETTER, STATE>> scc,
			final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries)
					throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNwars = nwars;
		final Set<SuccInfo> forbiddenSummaries = Collections.emptySet();
		final LoopFinder lf = new LoopFinder(honda, scc, true,
				acceptingSummaries, forbiddenSummaries);
		final NestedRun<LETTER, STATE> loop = lf.getNestedRun();
		assert loop.getLength() > 1 : "looping epsilon transition";
		final NestedRun<LETTER, STATE> stem =
				(new RunConstructor<LETTER, STATE>(mServices, mNwars, honda)).constructRun();
		mLogger.debug("Stem length: " + stem.getLength());
		mLogger.debug("Loop length: " + loop.getLength());
		mNlr = new NestedLassoRun<LETTER, STATE>(stem, loop);
		mLogger.debug("Stem " + stem);
		mLogger.debug("Loop " + loop);
		try {
			assert (new BuchiAccepts<LETTER, STATE>(mServices, mNwars, mNlr.getNestedLassoWord())).getResult();
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}
	
	NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
		return mNlr;
	}
	
	class LoopFinder extends RunFinder {
		private final StronglyConnectedComponent<StateContainer<LETTER, STATE>> mScc;
		
		public LoopFinder(final StateContainer<LETTER, STATE> goal,
				final StronglyConnectedComponent<StateContainer<LETTER, STATE>> scc,
				final boolean visitAccepting,
				final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries,
				final Set<SuccInfo> forbiddenSummaries) {
			super(goal, goal, visitAccepting, acceptingSummaries, forbiddenSummaries);
			mScc = scc;
		}
		
		@Override
		protected int getMaximalIterationNumber() {
			return mScc.getNodes().size();
		}
		
		@Override
		protected SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> succSc,
				final IncomingReturnTransition<LETTER, STATE> inTrans,
				final boolean summaryUsed, final boolean isGuaranteed) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getHierPred());
			final StateContainer<LETTER, STATE> linPredSc = mNwars.obtainSC(inTrans.getLinPred());
			return possiblePredecessor(predSc, inTrans.getLetter(), succSc,
					InCaRe.SUMMARY, linPredSc, true, isGuaranteed);
		}
		
		@Override
		protected SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> succSc,
				final IncomingCallTransition<LETTER, STATE> inTrans,
				final boolean summaryUsed, final boolean isGuaranteed) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getPred());
			return possiblePredecessor(predSc, inTrans.getLetter(), succSc,
					InCaRe.CALL, null, summaryUsed, isGuaranteed);
		}
		
		@Override
		protected SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> succSc,
				final IncomingInternalTransition<LETTER, STATE> inTrans,
				final boolean summaryUsed, final boolean isGuaranteed) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getPred());
			return possiblePredecessor(predSc, inTrans.getLetter(), succSc,
					InCaRe.INTERNAL, null, summaryUsed, isGuaranteed);
		}
		
		private SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> predSc,
				final LETTER letter,
				final StateContainer<LETTER, STATE> succSc, final InCaRe type,
				final StateContainer<LETTER, STATE> linPred,
				final boolean summaryUsed, final boolean isGuaranteedSucc) {
			if (!mScc.getNodes().contains(predSc)) {
				return null;
			}
			boolean isGuaranteedPred = isGuaranteedSucc;
			isGuaranteedPred = isGuaranteedPred || mNwars.isFinal(predSc.getState());
			if (type == InCaRe.SUMMARY) {
				isGuaranteedPred = isGuaranteedPred || isAcceptingSummary(predSc, succSc);
			}
			if (alreadyVisited(predSc, summaryUsed, isGuaranteedPred)) {
				return null;
			}
			final boolean goalFound = mGoal.equals(predSc) && isGuaranteedPred;
			final boolean guaranteeChanger = isGuaranteedSucc ^ isGuaranteedPred;
			final SuccInfo succInfo = new SuccInfo(succSc, letter, type, linPred,
					isGuaranteedPred, goalFound, guaranteeChanger);
			super.markVisited(predSc, summaryUsed, isGuaranteedPred);
			return succInfo;
		}
	}
	
	class SuccInfo {
		private final StateContainer<LETTER, STATE> mSuccessor;
		private final LETTER mLetter;
		private final InCaRe mType;
		private final StateContainer<LETTER, STATE> mLinPred;
		private final boolean mGuarantee;
		private final boolean mGoalFound;
		private final boolean mGuaranteeChanger;
		
		public SuccInfo(final StateContainer<LETTER, STATE> successor,
				final LETTER letter,
				final InCaRe type, final StateContainer<LETTER, STATE> linPred,
				final boolean guarantee,
				final boolean goalFound,
				final boolean guaranteeChanger) {
			if (type == InCaRe.SUMMARY && linPred == null) {
				throw new IllegalArgumentException("for summary we need linPred");
			}
			if ((type == InCaRe.INTERNAL || type == InCaRe.CALL) && linPred != null) {
				throw new IllegalArgumentException("linPred not allowed for internal and call");
			}
			if (type == InCaRe.RETURN) {
				throw new IllegalArgumentException("we do not use return here");
			}
			mSuccessor = successor;
			mLetter = letter;
			mType = type;
			mLinPred = linPred;
			mGuarantee = guarantee;
			mGoalFound = goalFound;
			mGuaranteeChanger = guaranteeChanger;
		}
		
		public StateContainer<LETTER, STATE> getSuccessor() {
			return mSuccessor;
		}
		
		public LETTER getLetter() {
			return mLetter;
		}
		
		public InCaRe getType() {
			return mType;
		}
		
		public StateContainer<LETTER, STATE> getLinPred() {
			return mLinPred;
		}
		
		public boolean isGuarantee() {
			return mGuarantee;
		}
		
		public boolean goalFound() {
			return mGoalFound;
		}
		
		public boolean isGuaranteeChanger() {
			return mGuaranteeChanger;
		}
		
		@Override
		public String toString() {
			return "SuccInfo [mSuccessor=" + mSuccessor + ", mLetter="
					+ mLetter + ", mType=" + mType + ", mLinPred="
					+ mLinPred + ", mGuarantee=" + mGuarantee
					+ ", mGoalFound=" + mGoalFound
					+ ", mGuaranteeChanger=" + mGuaranteeChanger + "]";
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + (mGoalFound ? 1231 : 1237);
			result = prime * result + (mGuarantee ? 1231 : 1237);
			result = prime * result + (mGuaranteeChanger ? 1231 : 1237);
			result = prime * result
					+ ((mLetter == null) ? 0 : mLetter.hashCode());
			result = prime * result
					+ ((mLinPred == null) ? 0 : mLinPred.hashCode());
			result = prime * result
					+ ((mSuccessor == null) ? 0 : mSuccessor.hashCode());
			result = prime * result
					+ ((mType == null) ? 0 : mType.hashCode());
			return result;
		}
		
		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final SuccInfo other = (SuccInfo) obj;
			if (!getOuterType().equals(other.getOuterType())) {
				return false;
			}
			if (mGoalFound != other.mGoalFound) {
				return false;
			}
			if (mGuarantee != other.mGuarantee) {
				return false;
			}
			if (mGuaranteeChanger != other.mGuaranteeChanger) {
				return false;
			}
			if (mLetter == null) {
				if (other.mLetter != null) {
					return false;
				}
			} else if (!mLetter.equals(other.mLetter)) {
				return false;
			}
			if (mLinPred == null) {
				if (other.mLinPred != null) {
					return false;
				}
			} else if (!mLinPred.equals(other.mLinPred)) {
				return false;
			}
			if (mSuccessor == null) {
				if (other.mSuccessor != null) {
					return false;
				}
			} else if (!mSuccessor.equals(other.mSuccessor)) {
				return false;
			}
			if (mType != other.mType) {
				return false;
			}
			return true;
		}
		
		private LassoExtractor<LETTER, STATE> getOuterType() {
			return LassoExtractor.this;
		}
	}
	
	abstract class RunFinder {
		
		protected final Set<SuccInfo> mForbiddenSummaries;
		
		protected final StateContainer<LETTER, STATE> mStart;
		protected final StateContainer<LETTER, STATE> mGoal;
		/**
		 * If true we search only for runs that visit an accepting state.
		 */
		protected final boolean mVisitAccepting;
		/**
		 * Successor mapping. If you build a path starting with this mapping
		 * it is guaranteed that the requirement (e.g., final state visited)
		 * is fulfilled. If you are rebuilding a run and requirement is
		 * already met, my may need mSuccessorsNoGuarantee for the
		 * remainder of the run.
		 * If there is no requirement all successor informations are in
		 * these Maps.
		 */
		//	protected final List<Map<STATE, Object>> mSuccessorsWithGuarantee;
		
		/**
		 * States that have already been visited (without start state) from
		 * which there is a run to the start state (of this search) such the
		 * equirement (e.g., final state visited) is fulfilled.
		 */
		//	protected final Set<STATE> mVisitedWithGuarantee;
		
		/**
		 * Successor mapping. I you use this to build a run, it is not
		 * guaranteed that the requirement (e.g., final state visited) is
		 * fulfilled.
		 */
		//	protected final List<Map<STATE, Object>> mSuccessorsNoGuarantee;
		
		/**
		 * States that have already been visited (without start state) from
		 * which there is a run to the start state (of this search) it is not
		 * guaranteed that the requirement (e.g., final state visited) is
		 * fulfilled.
		 */
		//	protected final Set<STATE> mVisitedNoGuarantee;
		
		/**
		 * Contains a pair of states (pre,post) if there is an run from
		 * pre to post such that
		 * - this run visits an accepting state
		 * - this run starts with a call
		 * - this run ends with a return
		 * <p>
		 * May be null if visiting an accepting state is not required.
		 */
		private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> mAcceptingSummaries;
		
		protected final List<Map<StateContainer<LETTER, STATE>, SuccInfo>> mSuccessorsWithSummary;
		protected final List<Map<StateContainer<LETTER, STATE>, SuccInfo>> mSuccessorsWithoutSummary;
		
		private final Set<StateContainer<LETTER, STATE>> mVisited_WithoutSummary_WithoutGuarantee =
				new HashSet<StateContainer<LETTER, STATE>>();
		private final Set<StateContainer<LETTER, STATE>> mVisited_WithSummary_WithoutGuarantee =
				new HashSet<StateContainer<LETTER, STATE>>();
		private final Set<StateContainer<LETTER, STATE>> mVisited_WithoutSummary_WithGuarantee =
				new HashSet<StateContainer<LETTER, STATE>>();
		private final Set<StateContainer<LETTER, STATE>> mVisited_WithSummary_WithGuarantee =
				new HashSet<StateContainer<LETTER, STATE>>();
				
		protected boolean mFoundWithSummary = false;
		protected boolean mFoundWithoutSummary = false;
		
		protected int mIteration;
		private int mIterationFoundWithSummary;
		
		public RunFinder(final StateContainer<LETTER, STATE> start,
				final StateContainer<LETTER, STATE> goal, final boolean visitAccepting,
				final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries,
				final Set<SuccInfo> forbiddenSummaries) {
			assert (start != null);
			assert (goal != null);
			mStart = start;
			mGoal = goal;
			mVisitAccepting = visitAccepting;
			mAcceptingSummaries = acceptingSummaries;
			mForbiddenSummaries = forbiddenSummaries;
			mSuccessorsWithSummary = new ArrayList<Map<StateContainer<LETTER, STATE>, SuccInfo>>();
			mSuccessorsWithoutSummary = new ArrayList<Map<StateContainer<LETTER, STATE>, SuccInfo>>();
			mIterationFoundWithSummary = -1;
			mIteration = 0;
		}
		
		public NestedRun<LETTER, STATE> getNestedRun() {
			find(mStart);
			if (mFoundWithoutSummary) {
				return constructRun(mIteration, false);
			} else {
				return constructRun(mIterationFoundWithSummary, true);
			}
		}
		
		protected boolean isAcceptingSummary(final StateContainer<LETTER, STATE> predSc,
				final StateContainer<LETTER, STATE> succSc) {
			final Set<Summary<LETTER, STATE>> summaries = mAcceptingSummaries.getImage(predSc);
			if (summaries == null) {
				return false;
			} else {
				for (final Summary<LETTER, STATE> summary : summaries) {
					if (summary.getSucc().equals(succSc)) {
						return true;
					}
					
				}
				return false;
			}
		}
		
		private boolean continueSearch() {
			if (mFoundWithoutSummary) {
				return false;
			}
			if (mSuccessorsWithSummary.get(mIteration).isEmpty()
					&& mSuccessorsWithoutSummary.get(mIteration).isEmpty()) {
				return false;
			}
			return true;
		}
		
		private void find(final StateContainer<LETTER, STATE> start) {
			mSuccessorsWithoutSummary.add(new HashMap<StateContainer<LETTER, STATE>, SuccInfo>());
			mSuccessorsWithSummary.add(new HashMap<StateContainer<LETTER, STATE>, SuccInfo>());
			findPredecessors(start, !mVisitAccepting || mNwars.isFinal(start.getState()), false);
			while (continueSearch()) {
				assert (mIteration <= getMaximalIterationNumber()) : "too many iterations";
				mIteration++;
				mSuccessorsWithoutSummary.add(new HashMap<StateContainer<LETTER, STATE>, SuccInfo>());
				mSuccessorsWithSummary.add(new HashMap<StateContainer<LETTER, STATE>, SuccInfo>());
				if (!mFoundWithSummary) {
					for (final StateContainer<LETTER, STATE> sc : mSuccessorsWithSummary.get(mIteration - 1).keySet()) {
						final boolean isGuaranteed = mSuccessorsWithSummary.get(mIteration - 1).get(sc).isGuarantee();
						findPredecessors(sc, isGuaranteed, true);
					}
				}
				for (final StateContainer<LETTER, STATE> sc : mSuccessorsWithoutSummary.get(mIteration - 1).keySet()) {
					final boolean isGuaranteed = mSuccessorsWithoutSummary.get(mIteration - 1).get(sc).isGuarantee();
					findPredecessors(sc, isGuaranteed, false);
				}
				
			}
			assert (mFoundWithSummary || mFoundWithoutSummary) : "Bug in run reconstruction of new emptiness test.";
		}
		
		protected abstract int getMaximalIterationNumber();
		
		protected abstract SuccInfo possiblePredecessor(
				StateContainer<LETTER, STATE> succSc,
				IncomingReturnTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteed);
				
		protected abstract SuccInfo possiblePredecessor(
				StateContainer<LETTER, STATE> succSc,
				IncomingCallTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteed);
				
		protected abstract SuccInfo possiblePredecessor(
				StateContainer<LETTER, STATE> succSc,
				IncomingInternalTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteed);
				
		/**
		 * Add for a predecessor predSc information about successors to succMap.
		 * If there is already a successor information that is as good as this
		 * (requirement already fulfilled) nothing is added.
		 * 
		 * @param type
		 *            call, internal, or summary
		 * @param linPred
		 *            linear predecessor if type is summary
		 * @param succSc
		 *            successor state
		 * @param isGuranteed
		 *            is the requirement (e.g., accepting state) visited
		 *            guaranteed?
		 */
		private void addSuccessorInformation(final StateContainer<LETTER, STATE> predSc,
				final boolean summaryUsed,
				final SuccInfo newSuccInfo) {
			Map<StateContainer<LETTER, STATE>, SuccInfo> succMap;
			if (summaryUsed) {
				mFoundWithSummary |= newSuccInfo.goalFound();
				succMap = mSuccessorsWithSummary.get(mIteration);
			} else {
				mFoundWithoutSummary |= newSuccInfo.goalFound();
				succMap = mSuccessorsWithoutSummary.get(mIteration);
			}
			final SuccInfo current = succMap.get(predSc);
			if (current == null) {
				succMap.put(predSc, newSuccInfo);
				return;
			}
			if (!current.isGuarantee() && newSuccInfo.isGuarantee()) {
				succMap.put(predSc, newSuccInfo);
				return;
			}
			if (!current.goalFound() && newSuccInfo.goalFound()) {
				succMap.put(predSc, newSuccInfo);
				return;
			}
		}
		
		private void markVisited(final StateContainer<LETTER, STATE> sc,
				final boolean summaryUsed, final boolean isGuranteed) {
			if (summaryUsed) {
				if (isGuranteed) {
					mVisited_WithSummary_WithGuarantee.add(sc);
				} else {
					mVisited_WithSummary_WithoutGuarantee.add(sc);
				}
			} else {
				if (isGuranteed) {
					mVisited_WithoutSummary_WithGuarantee.add(sc);
				} else {
					mVisited_WithoutSummary_WithoutGuarantee.add(sc);
				}
			}
		}
		
		protected boolean alreadyVisited(final StateContainer<LETTER, STATE> sc,
				final boolean summaryUsed, final boolean isGuranteed) {
			if (summaryUsed) {
				if (isGuranteed) {
					return mVisited_WithSummary_WithGuarantee.contains(sc);
				} else {
					return mVisited_WithSummary_WithoutGuarantee.contains(sc);
				}
			} else {
				if (isGuranteed) {
					return mVisited_WithoutSummary_WithGuarantee.contains(sc);
				} else {
					return mVisited_WithoutSummary_WithoutGuarantee.contains(sc);
				}
			}
		}
		
		protected void findPredecessors(final StateContainer<LETTER, STATE> sc,
				final boolean isGuaranteed, final boolean summaryUsed) {
			for (final IncomingInternalTransition<LETTER, STATE> inTrans : mNwars.internalPredecessors(sc.getState())) {
				final SuccInfo succInfo = possiblePredecessor(sc, inTrans, summaryUsed, isGuaranteed);
				if (succInfo != null) {
					final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getPred());
					addSuccessorInformation(predSc, summaryUsed, succInfo);
				}
			}
			for (final IncomingCallTransition<LETTER, STATE> inTrans : mNwars.callPredecessors(sc.getState())) {
				final SuccInfo succInfo = possiblePredecessor(sc, inTrans, summaryUsed, isGuaranteed);
				if (succInfo != null) {
					final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getPred());
					addSuccessorInformation(predSc, summaryUsed, succInfo);
				}
			}
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : mNwars.returnPredecessors(sc.getState())) {
				final SuccInfo succInfo = possiblePredecessor(sc, inTrans, summaryUsed, isGuaranteed);
				if (succInfo != null) {
					final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getHierPred());
					addSuccessorInformation(predSc, true, succInfo);
				}
			}
			if (mFoundWithSummary && mIterationFoundWithSummary == -1) {
				mIterationFoundWithSummary = mIteration;
			}
		}
		
		/**
		 * Construct the run that has been found.
		 * 
		 * @return nested run
		 */
		private NestedRun<LETTER, STATE> constructRun(final int iteration, final boolean foundWithSummary) {
			boolean visitAcceptingStillRequired = mVisitAccepting;
			NestedRun<LETTER, STATE> result = new NestedRun<LETTER, STATE>(mGoal.getState());
			
			for (int i = iteration; i >= 0; i--) {
				final StateContainer<LETTER, STATE> currentState =
						mNwars.obtainSC(result.getStateAtPosition(result.getLength() - 1));
				if (mNwars.isFinal(currentState.getState())) {
					visitAcceptingStillRequired = false;
				}
				SuccInfo succs = null;
				if (foundWithSummary) {
					succs = mSuccessorsWithSummary.get(i).get(currentState);
				}
				if (succs == null) {
					succs = mSuccessorsWithoutSummary.get(i).get(currentState);
				}
				assert succs != null : "No successor found!";
				NestedRun<LETTER, STATE> newSuffix;
				if (succs.getType() == InCaRe.INTERNAL) {
					newSuffix = new NestedRun<LETTER, STATE>(currentState.getState(),
							succs.getLetter(),
							NestedWord.INTERNAL_POSITION,
							succs.getSuccessor().getState());
				} else if (succs.getType() == InCaRe.CALL) {
					newSuffix = new NestedRun<LETTER, STATE>(currentState.getState(),
							succs.getLetter(),
							NestedWord.PLUS_INFINITY,
							succs.getSuccessor().getState());
				} else if (succs.getType() == InCaRe.SUMMARY) {
					boolean findAcceptingSummary;
					if (visitAcceptingStillRequired && succs.isGuaranteeChanger()
							&& !mNwars.isFinal(currentState.getState())) {
						assert (isAcceptingSummary(currentState, succs.getSuccessor()));
						findAcceptingSummary = true;
					} else {
						findAcceptingSummary = false;
					}
					final Set<SuccInfo> forbiddenSummaries = new HashSet<SuccInfo>();
					forbiddenSummaries.addAll(mForbiddenSummaries);
					assert !forbiddenSummaries.contains(succs);
					forbiddenSummaries.add(succs);
					final SummaryFinder summaryFinder = new SummaryFinder(
							succs.getLinPred(), currentState,
							findAcceptingSummary, mAcceptingSummaries,
							forbiddenSummaries);
					newSuffix = summaryFinder.getNestedRun();
					final NestedRun<LETTER, STATE> retSuffix =
							new NestedRun<LETTER, STATE>(
									succs.getLinPred().getState(),
									succs.getLetter(),
									NestedWord.MINUS_INFINITY,
									succs.getSuccessor().getState());
					newSuffix = newSuffix.concatenate(retSuffix);
					if (findAcceptingSummary) {
						visitAcceptingStillRequired = false;
					}
				} else {
					throw new AssertionError("unknown transition");
				}
				result = result.concatenate(newSuffix);
			}
			return result;
		}
	}
	
	class SummaryFinder extends RunFinder {
		
		public SummaryFinder(final StateContainer<LETTER, STATE> returnPredecessor,
				final StateContainer<LETTER, STATE> callPredecessor,
				final boolean visitAccepting,
				final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries,
				final Set<SuccInfo> forbiddenSummaries) {
			super(returnPredecessor, callPredecessor, visitAccepting, acceptingSummaries, forbiddenSummaries);
		}
		
		@Override
		protected int getMaximalIterationNumber() {
			return mNwars.size();
		}
		
		@Override
		protected SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> succSc,
				final IncomingInternalTransition<LETTER, STATE> inTrans,
				final boolean summaryUsed, final boolean isGuaranteedSucc) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getPred());
			if (!goalIsDownState(predSc, isGuaranteedSucc)) {
				return null;
			}
			boolean isGuaranteedPred = isGuaranteedSucc;
			isGuaranteedPred = isGuaranteedPred || mNwars.isFinal(predSc.getState());
			if (alreadyVisited(predSc, summaryUsed, isGuaranteedPred)) {
				return null;
			}
			final boolean guaranteeChanger = isGuaranteedPred ^ isGuaranteedSucc;
			final SuccInfo succInfo = new SuccInfo(succSc, inTrans.getLetter(),
					InCaRe.INTERNAL, null, isGuaranteedPred, false, guaranteeChanger);
			super.markVisited(predSc, summaryUsed, isGuaranteedPred);
			return succInfo;
		}
		
		@Override
		protected SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> succSc,
				final IncomingCallTransition<LETTER, STATE> inTrans,
				final boolean summaryUsed, final boolean isGuaranteedSucc) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getPred());
			if (!isGuaranteedSucc || !mGoal.equals(predSc)) {
				return null;
			}
			final SuccInfo succInfo = new SuccInfo(succSc, inTrans.getLetter(),
					InCaRe.CALL, null, isGuaranteedSucc, true, false);
			super.markVisited(predSc, summaryUsed, isGuaranteedSucc);
			return succInfo;
		}
		
		@Override
		protected SuccInfo possiblePredecessor(final StateContainer<LETTER, STATE> succSc,
				final IncomingReturnTransition<LETTER, STATE> inTrans,
				final boolean summaryUsed, final boolean isGuaranteedSucc) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainSC(inTrans.getHierPred());
			if (!goalIsDownState(predSc, isGuaranteedSucc)) {
				return null;
			}
			boolean isGuaranteedPred = isGuaranteedSucc;
			isGuaranteedPred = isGuaranteedPred || mNwars.isFinal(predSc.getState());
			isGuaranteedPred = isGuaranteedPred || isAcceptingSummary(predSc, succSc);
			if (alreadyVisited(predSc, true, isGuaranteedPred)) {
				return null;
			}
			final boolean guaranteeChanger = isGuaranteedPred ^ isGuaranteedSucc;
			final StateContainer<LETTER, STATE> linPredSc = mNwars.obtainSC(inTrans.getLinPred());
			final SuccInfo succInfo = new SuccInfo(succSc, inTrans.getLetter(),
					InCaRe.SUMMARY, linPredSc, isGuaranteedPred, false, guaranteeChanger);
			if (mForbiddenSummaries.contains(succInfo)) {
				return null;
			}
			super.markVisited(predSc, true, isGuaranteedPred);
			return succInfo;
		}
		
		private boolean goalIsDownState(final StateContainer<LETTER, STATE> predSc, final boolean isGuranteed) {
			if (!predSc.getDownStates().containsKey(mGoal.getState())) {
				return false;
			}
			if (isGuranteed) {
				return true;
			} else {
				return predSc.hasDownProp(mGoal.getState(),
						DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL);
			}
		}
		
	}
	
}
