/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IDeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.TreeRelation;

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKVNwa<LETTER,STATE> implements INestedWordAutomatonSimple<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is sufficient, see paper of Seth Forgaty.
	 */
	private final int m_UserDefinedMaxRank;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	
	private final NestedWordAutomatonCache<LETTER, STATE> m_Cache;
	
	StateFactory<STATE> m_StateFactory;
	
	/**
	 * Maps DeterminizedState to its representative in the resulting automaton.
	 */
	private final Map<DeterminizedState<LETTER,STATE>,STATE> m_det2res =
		new HashMap<DeterminizedState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the FkvSubsetComponentState for which it
	 * was created.
	 */
	private final Map<STATE,FkvSubsetComponentState<LETTER,STATE>> m_res2scs =
		new HashMap<STATE, FkvSubsetComponentState<LETTER,STATE>>();
	
	/**
	 * Maps a LevelRankingState to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState<LETTER,STATE>,STATE> m_lrk2res =
		new HashMap<LevelRankingState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the LevelRankingState for which it
	 * was created.
	 */
	private final Map<STATE,LevelRankingState<LETTER,STATE>> m_res2lrk =
		new HashMap<STATE, LevelRankingState<LETTER,STATE>>();
	
	private final IStateDeterminizer<LETTER,STATE> m_StateDeterminizer;
	
	/**
	 * Highest rank that occured during the construction. Used only for
	 *  statistics.
	 */
	int m_HighestRank = -1;	
	
	
	
	
	public BuchiComplementFKVNwa(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> operand,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			StateFactory<STATE> stateFactory, int userDefinedMaxRank) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_StateFactory = stateFactory;
		m_Cache = new NestedWordAutomatonCache<LETTER, STATE>(
				m_Services,
				operand.getInternalAlphabet(), operand.getCallAlphabet(), 
				operand.getReturnAlphabet(), m_StateFactory);
		m_StateDeterminizer = stateDeterminizer;
		m_UserDefinedMaxRank = userDefinedMaxRank;
	}
	
	
	private void constructInitialState() {
		DeterminizedState<LETTER,STATE> detState = m_StateDeterminizer.initialState();
		getOrAdd(detState, true, false);	
	}
	

	/**
	 * Return state of result automaton that represents lrkState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(LevelRankingState<LETTER, STATE> lrkState) {
		STATE resSucc = m_lrk2res.get(lrkState);
		if (resSucc == null) {
			resSucc = m_StateFactory.buchiComplementFKV(lrkState);
			assert resSucc != null;
			m_Cache.addState(false, lrkState.isOempty(), resSucc);
			m_lrk2res.put(lrkState, resSucc);
			m_res2lrk.put(resSucc, lrkState);
			if (this.m_HighestRank < lrkState.m_HighestRank) {
				this.m_HighestRank = lrkState.m_HighestRank;
			}
		}
		return resSucc;
	}
	
	
	/**
	 * Return state of result automaton that represents detState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(DeterminizedState<LETTER,STATE> detState, 
			boolean isInitial, boolean isFinal) {
		assert !isFinal || detState.isEmpty() : "only the sink state is final";
		STATE resSucc = m_det2res.get(detState);
		if (resSucc == null) {
			resSucc = m_StateDeterminizer.getState(detState);
			assert resSucc != null;
			m_Cache.addState(isInitial, isFinal, resSucc);
			m_det2res.put(detState, resSucc);
			m_res2scs.put(resSucc, new FkvSubsetComponentState<>(detState));
		}
		return resSucc;
	}
	
	public int getHighesRank() {
		return m_HighestRank;
	}

	public int getPowersetStates() {
		return m_res2scs.size();
	}

	public int getRankStates() {
		return m_res2lrk.size();
	}
	


	@Override
	public Iterable<STATE> getInitialStates() {
		constructInitialState();
		return m_Cache.getInitialStates();
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return m_Cache.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_Cache.isFinal(state);
	}



	@Override
	public STATE getEmptyStackState() {
		return m_Cache.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_Operand.getReturnAlphabet();
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			Collection<STATE> resSuccs = new ArrayList<STATE>();
			FkvSubsetComponentState<LETTER,STATE> detUp = m_res2scs.get(state);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = m_StateDeterminizer.internalSuccessor(
							detUp.getDeterminizedState(), letter);
					boolean isAccepting = detSucc.isEmpty();
					STATE resSucc = getOrAdd(detSucc, false, isAccepting);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
				LevelRankingConstraint<LETTER,STATE> constraints = new LevelRankingConstraint<LETTER,STATE>(
						m_Operand, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.internalSuccessorConstraints(detUp, letter);
				TightLevelRankingStateGenerator gen = 
					new HeiMatTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState<LETTER,STATE>> result = gen.computeResult();
				if (result.size() > 2) {
					m_Logger.warn("big" + result.size());
				}
				for (LevelRankingState<LETTER,STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState<LETTER,STATE> complUp = m_res2lrk.get(state);
			if (complUp != null) {
				LevelRankingConstraint<LETTER,STATE> constraints = new LevelRankingConstraint<LETTER,STATE>(
						m_Operand, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.internalSuccessorConstraints(complUp, letter);
				TightLevelRankingStateGenerator gen = 
					new HeiMatTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState<LETTER,STATE>> result = gen.computeResult();
				if (result.size() > 4) {
					m_Logger.warn("big" + result.size());
				}
				for (LevelRankingState<LETTER,STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return m_Cache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		for (LETTER letter : getInternalAlphabet()) {
			internalSuccessors(state, letter);
		}
		return m_Cache.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succCall(state, letter);
		if (succs == null) {
			Collection<STATE> resSuccs = new ArrayList<STATE>();
			FkvSubsetComponentState<LETTER,STATE> detUp = m_res2scs.get(state);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = m_StateDeterminizer.callSuccessor(
							detUp.getDeterminizedState(), letter);
					boolean isAccepting = detSucc.isEmpty();
					STATE resSucc = getOrAdd(detSucc, false, isAccepting);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraint<LETTER, STATE>(
						m_Operand, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.callSuccessorConstraints(detUp, letter);
				TightLevelRankingStateGenerator gen = 
					new HeiMatTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState<LETTER, STATE>> result = gen.computeResult();
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState<LETTER, STATE> complUp = m_res2lrk.get(state);
			if (complUp != null) {
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraint<LETTER, STATE>(
						m_Operand, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.callSuccessorConstraints(complUp, letter);
				TightLevelRankingStateGenerator gen = 
					new HeiMatTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState<LETTER, STATE>> result = gen.computeResult();
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return m_Cache.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		for (LETTER letter : getCallAlphabet()) {
			callSuccessors(state, letter);
		}
		return m_Cache.callSuccessors(state);
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		Collection<STATE> succs = m_Cache.succReturn(state, hier, letter);
		if (succs == null) {
			Collection<STATE> resSuccs = new ArrayList<STATE>();
			FkvSubsetComponentState<LETTER,STATE> detUp = m_res2scs.get(state);
			FkvSubsetComponentState<LETTER,STATE> detDown = m_res2scs.get(hier);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = m_StateDeterminizer.returnSuccessor(
							detUp.getDeterminizedState(), detDown.getDeterminizedState(), letter);
					boolean isAccepting = detSucc.isEmpty();
					STATE resSucc = getOrAdd(detSucc, false, isAccepting);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraint<LETTER, STATE>(
						m_Operand, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.returnSuccessorConstraints(detUp, detDown, letter);
				TightLevelRankingStateGenerator gen = 
					new HeiMatTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState<LETTER, STATE>> result = gen.computeResult();
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState<LETTER, STATE> complUp = m_res2lrk.get(state);
			IFkvState<LETTER, STATE> complDown;
			if (m_res2scs.containsKey(hier)) {
				complDown = m_res2scs.get(hier);
			} else {
				assert m_res2lrk.containsKey(hier);
				complDown = m_res2lrk.get(hier);
			}
			if (complUp != null) {
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraint<LETTER, STATE>(
						m_Operand, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.returnSuccessorConstraints(complUp, complDown, letter);
				TightLevelRankingStateGenerator gen = 
					new HeiMatTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState<LETTER, STATE>> result = gen.computeResult();
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return m_Cache.returnSucccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		for (LETTER letter : getReturnAlphabet()) {
			returnSucccessors(state, hier, letter);
		}
		return m_Cache.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		return m_Cache.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}
	
	
	
	/**
	 * Generates all LevelRanking states that are tight (see 2004ATVA paper)
	 * and fulfill given LevelRankingConstraints.
	 */
	private class TightLevelRankingStateGenerator {

		private final List<DoubleDecker<StateWithRankInfo<STATE>>> m_UnrestrictedDoubleDeckerWithRankInfo = 
			new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
		private final List<Integer> m_UnrestrictedMaxRank = 
			new ArrayList<Integer>();
		protected int[] m_UnrestrictedRank;
		
		private final List<DoubleDecker<StateWithRankInfo<STATE>>> m_RestrictedDoubleDeckerWithRankInfo = 
			new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
		protected final List<Integer> m_RestrictedMaxRank = 
			new ArrayList<Integer>();
		protected int[] m_RestrictedRank;
		
		protected final List<LevelRankingState<LETTER,STATE>> m_Result =
			new ArrayList<LevelRankingState<LETTER,STATE>>();
		protected final LevelRankingConstraint<LETTER,STATE> m_Constraint;
		
		public TightLevelRankingStateGenerator(LevelRankingConstraint<LETTER,STATE> constraint) {
			m_Constraint = constraint;
			partitionIntoRestrictedAndUnrestricted();
		}
		

		Collection<LevelRankingState<LETTER,STATE>> computeResult() {
//			m_Logger.debug("Constructing LevelRankings for" + 
//									m_UnrestrictedDoubleDeckerWithRankInfo.toString() + 
//									m_RestrictedDoubleDeckerWithRankInfo.toString());
			
			if (m_UnrestrictedRank.length == 0 && m_RestrictedRank.length == 0) {
				constructComplementState();
				return m_Result;
			}
			
			initializeUnrestricted();
			boolean overflowUnrestricted;
			do {
				int highestOddRank = getMaxNatOrZero(m_UnrestrictedRank);
				if (highestOddRank % 2 == 1 && 
						isOntoOddNatsUpToX(m_UnrestrictedRank, highestOddRank)) {
					initializeRestricted(highestOddRank);
					boolean overflowRestricted;
					do {
						constructComplementState();
						overflowRestricted = 
									increaseCounterRestricted(highestOddRank);
					}
					while (!overflowRestricted);					
				}
				overflowUnrestricted = increaseCounterUnrestricted();
			}
			while (!overflowUnrestricted);
			return m_Result;
		}

		/**
		 * Partition DoubleDeckerWithRankInfo into Restricted and Unrestricted.
		 * A double Decker is restricted iff is has to have an even rank in
		 * each LevelRankingState defined by this LevelRankingConstraint.
		 */
		private void partitionIntoRestrictedAndUnrestricted() {
			for (StateWithRankInfo<STATE> down : m_Constraint.getDownStates()) {
				for (StateWithRankInfo<STATE> up : m_Constraint.getUpStates(down)) {
					Integer rank = up.getRank();
					if (m_Operand.isFinal(up.getState()) || rank == 0) {
						m_RestrictedDoubleDeckerWithRankInfo.add(
											new DoubleDecker<StateWithRankInfo<STATE>>(down, up));
						m_RestrictedMaxRank.add(rank);
					}
					else {
						m_UnrestrictedDoubleDeckerWithRankInfo.add(
											new DoubleDecker<StateWithRankInfo<STATE>>(down, up));
						m_UnrestrictedMaxRank.add(rank);
					}
				}
			}
			
			m_UnrestrictedRank = new int[m_UnrestrictedMaxRank.size()];
			m_RestrictedRank = new int[m_RestrictedMaxRank.size()];
		}
		
		private void constructComplementState() {
//			m_Logger.debug("Rank " + Arrays.toString(m_UnrestrictedRank) + 
//											Arrays.toString(m_RestrictedRank));
			LevelRankingState<LETTER,STATE> result = new LevelRankingState<LETTER,STATE>(m_Operand);
			for (int i=0; i<m_RestrictedRank.length; i++) {
				DoubleDecker<StateWithRankInfo<STATE>> dd = m_RestrictedDoubleDeckerWithRankInfo.get(i);
				StateWithRankInfo<STATE> down = dd.getDown();
				StateWithRankInfo<STATE> up = dd.getUp();
				int rank = m_RestrictedRank[i];
				boolean addToO = m_Constraint.inO(down, up.getState());
				result.addRank(down, up.getState(), rank, addToO);
			}
			
			for (int i=0; i<m_UnrestrictedRank.length; i++) {
				DoubleDecker<StateWithRankInfo<STATE>> dd = m_UnrestrictedDoubleDeckerWithRankInfo.get(i);
				StateWithRankInfo<STATE> down = dd.getDown();
				StateWithRankInfo<STATE> up = dd.getUp();
				int rank = m_UnrestrictedRank[i];
				boolean addToO = m_Constraint.inO(down, up.getState()) && (rank % 2 == 0);
				result.addRank(down, up.getState(), rank, addToO);
			}
			m_Result.add(result);
		}
		
		/**
		 * @return maximal entry in given array, 0 if array is empty or maximum
		 * is < 0
		 */
		private int getMaxNatOrZero(int[] array) {
			int max = 0;
			for (int i=0; i<array.length; i++) {
				if (array[i] > max) {
					max = array[i];
				}
			}
			return max;
		}
		
		
		/**
		 * @param array of natural numbers
		 * @param an odd number
		 * @return true iff every odd number from 1 up to x (including x) occurs
		 *  in array.
		 */
		private boolean isOntoOddNatsUpToX(int[] array, int x) {
			assert (x % 2 ==1);
			int[] occurrence = new int[x+1];
			for (int i=0; i<array.length; i++) {
				occurrence[array[i]]++;
			}
			for (int i=1; i<=x; i=i+2) {
				if (occurrence[i] == 0) {
					return false;
				}
			}
			return true;
		}
		

		
		protected void initializeUnrestricted() {
			for (int i=0; i < m_UnrestrictedRank.length; i++) {
				m_UnrestrictedRank[i] = 0;
			}
		}
		
		protected void initializeRestricted(int highestOddRank) {
			for (int i=0; i < m_RestrictedRank.length; i++) {
				m_RestrictedRank[i] = 0;
			}
		}
		
		
		/**
		 * @return true if overflow occured and therefore counter was reset
		 * or counter has length 0 
		 */
		private boolean increaseCounterUnrestricted() {
			if (m_UnrestrictedRank.length == 0) {
				return true;
			}
			boolean overflow;
			int pos = 0;
			do {
				overflow = increaseDigitUnrestricted(pos);
				pos++;
			}
			while(overflow && pos < m_UnrestrictedRank.length);
			return overflow;
		}
		
		protected boolean increaseDigitUnrestricted(int pos) {
			int oldDigit = m_UnrestrictedRank[pos];
			int newDigit = oldDigit + 1;
			assert (maxTightRankUnrestricted(pos) >= 1);
			if (newDigit <= maxTightRankUnrestricted(pos)) {
				m_UnrestrictedRank[pos] = newDigit;
				return false;
			}
			else {
				m_UnrestrictedRank[pos] = 0;
				return true;
			}
		}
		

		
		/**
		 * @return true if overflow occured and therefore counter was reset
		 * 	 or counter has length 0 
		 */
		protected boolean increaseCounterRestricted(int highestOddRank) {
			if (m_RestrictedRank.length == 0) {
				return true;
			}
			boolean overflow;
			int pos = 0;
			do {
				overflow = increaseDigitRestricted(pos, highestOddRank);
				pos++;
			}
			while(overflow && pos < m_RestrictedRank.length);
			return overflow;
		}
		
		private boolean increaseDigitRestricted(int pos, int highestOddRank) {
			int oldDigit = m_RestrictedRank[pos];
			int newDigit = oldDigit + 2;
			if (newDigit <= maxTightRankRestricted(pos, highestOddRank)) {
				m_RestrictedRank[pos] = newDigit;
				return false;
			}
			else {
				m_RestrictedRank[pos] = 0;
				return true;
			}
		}
		
		
		protected int maxTightRankUnrestricted(int i) {
			int numberOfStatesDefinedMaxRank = m_UnrestrictedMaxRank.size() * 2 -1;
			if (numberOfStatesDefinedMaxRank <= m_UserDefinedMaxRank) {
				if (m_UnrestrictedMaxRank.get(i) <= numberOfStatesDefinedMaxRank ) {
					return m_UnrestrictedMaxRank.get(i);
				}
				else {
					return numberOfStatesDefinedMaxRank;
				}
			}
			else {
				if (m_UnrestrictedMaxRank.get(i) <= m_UserDefinedMaxRank ) {
					return m_UnrestrictedMaxRank.get(i);
				}
				else {
					return m_UserDefinedMaxRank;
				}
			}
		}
		

		private int maxTightRankRestricted(int i, int highestOddRank) {
			if (highestOddRank <= m_UserDefinedMaxRank) {
				if (m_RestrictedMaxRank.get(i) <= highestOddRank ) {
					return m_RestrictedMaxRank.get(i);
				}
				else {
					return highestOddRank;
				}
			}
			else {
				if (m_RestrictedMaxRank.get(i) <= m_UserDefinedMaxRank ) {
					return m_RestrictedMaxRank.get(i);
				}
				else {
					return m_UserDefinedMaxRank;
				}
			}
		}
	}
	


	
	
	
	
	
	
	
	
	
	
	
	/**
	 * Generates all LevelRanking states that are tight (see 2004ATVA paper),
	 * fulfill given LevelRankingConstraints and fulfill the following property:
	 * If a DoubleDeckerWithRankInfo has an even rank it must the the highest possible even
	 * rank.
	 * Warning: I think a restriction to LevelRanking that satisfy also the
	 * latter property leads to a sound complementation, but it is not mentioned
	 * in any paper and I do not have a proof for that. 
	 */
	private class MatthiasTightLevelRankingStateGenerator extends
											TightLevelRankingStateGenerator {

		public MatthiasTightLevelRankingStateGenerator(
						LevelRankingConstraint<LETTER,STATE> constraints) {
			super(constraints);
		}

		@Override
		protected void initializeRestricted(int highestOddRank) {
			if (highestOddRank == 0) {
				for (int i=0; i < m_RestrictedRank.length; i++) {
					m_RestrictedRank[i] = 0;
				}
			}
			else {		
				assert (highestOddRank > 0 && highestOddRank % 2 == 1);
				for (int i=0; i < m_RestrictedRank.length; i++) {
					if (highestOddRank < m_RestrictedMaxRank.get(i)) {
						m_RestrictedRank[i] = highestOddRank -1;
					}
					else {
						if (m_RestrictedMaxRank.get(i) % 2 == 1) {
							m_RestrictedRank[i] = m_RestrictedMaxRank.get(i)-1;
						}
						else {
							m_RestrictedRank[i] = m_RestrictedMaxRank.get(i);
						}
					}
				}
			}
		}
		

		@Override
		protected boolean increaseDigitUnrestricted(int pos) {
				int oldDigit = m_UnrestrictedRank[pos];
				if (oldDigit == maxTightRankUnrestricted(pos)) {
					m_UnrestrictedRank[pos] = 1;
					return true;
				}
				else {
					int newDigit;
					assert (maxTightRankUnrestricted(pos) >= 1);
					if (oldDigit + 2 <= maxTightRankUnrestricted(pos)) {
						newDigit = oldDigit + 2;
					}
					else {
						newDigit = oldDigit + 1;
						assert (newDigit == maxTightRankUnrestricted(pos));
						assert (newDigit % 2 == 0);
					}
					m_UnrestrictedRank[pos] = newDigit;
					return false;
				}
		}

		@Override
		protected boolean increaseCounterRestricted(int highestOddRank) {
			return true;
		}

		@Override
		protected void initializeUnrestricted() {
			for (int i=0; i < m_UnrestrictedRank.length; i++) {
				m_UnrestrictedRank[i] = 1;
			}
		}
	}


	private class HeiMatTightLevelRankingStateGenerator extends
		TightLevelRankingStateGenerator {
		
		private final TreeRelation<Integer, DoubleDecker<StateWithRankInfo<STATE>>> m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo;
		private boolean m_SuccessorsOfFinalsWantToLeaveO = true;
//		private final int numberOfDoubleDeckerWithRankInfos;

		public HeiMatTightLevelRankingStateGenerator(LevelRankingConstraint<LETTER,STATE> constraint) {
			super(constraint);
			m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo = new TreeRelation<Integer, DoubleDecker<StateWithRankInfo<STATE>>>();
//			numberOfDoubleDeckerWithRankInfos = super.m_UnrestrictedDoubleDeckerWithRankInfo.size();
			for (DoubleDecker<StateWithRankInfo<STATE>> dd : super.m_UnrestrictedDoubleDeckerWithRankInfo) {
				Integer rank = constraint.m_LevelRanking.get(dd.getDown()).get(dd.getUp().getState());
				m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.addPair(rank, dd);
			}
		}
		
		
		
		@Override
		Collection<LevelRankingState<LETTER,STATE>> computeResult() {
			int unassignedUnrestricted = m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.size();
			if (unassignedUnrestricted == 0) {
				// all possible states are accepting or have rank 0
				// no state with odd rank possible, hence not tight - no successors
				return Collections.emptyList();
			}
			LevelRankingWithSacrificeInformation lrwsi = new LevelRankingWithSacrificeInformation();
			int assignedUnrestricted = 0;
			recursivelyComputeResults(0, lrwsi, assignedUnrestricted, unassignedUnrestricted);
			return m_Result;
		}
		
		/**
		 * Returns all unrestricted DoubleDeckerWithRankInfos whose rank is rk.
		 */
		private DoubleDecker<StateWithRankInfo<STATE>>[] getUnrestrictedWithMaxRank(int rank) {
			DoubleDecker<StateWithRankInfo<STATE>>[] result;
			@SuppressWarnings("unchecked")
			DoubleDecker<StateWithRankInfo<STATE>>[] emptyDoubleDeckerWithRankInfoArray = new DoubleDecker[0];
			if (m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.getDomain().contains(rank)) {
				result = m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.getImage(rank).toArray(emptyDoubleDeckerWithRankInfoArray);
			} else {
				result = emptyDoubleDeckerWithRankInfoArray; 
			}
			return result;
		}

		
		/**
		 * Construct all stuffed levelRankings that are compatible with the
		 * partially constructed levelRanking lrwsi.
		 * In this iteration, we assign the (even) rank rk and the (odd)
		 * rank rk-1.
		 * @param rk even rank such that all (odd?) ranks <rk-2 have already 
		 * been assigned
		 * @param lrwsi
		 * @param assignedUnrestricted unrestricted DoubleDeckerWithRankInfos whose rank is
		 * already assigned  
		 * @param unassignedUnrestricted restricted DoubleDeckerWithRankInfos whose rank is
		 * not yet assigned
		 */
		private void recursivelyComputeResults(final Integer rk, final LevelRankingWithSacrificeInformation lrwsi, 
				int assignedUnrestricted, int unassignedUnrestricted) {
			assert rk % 2 == 0;
			assert assignedUnrestricted + unassignedUnrestricted == super.m_UnrestrictedDoubleDeckerWithRankInfo.size();
			
			DoubleDecker<StateWithRankInfo<STATE>>[] constraintToRank = getUnrestrictedWithMaxRank(rk);
			if (unassignedUnrestricted == constraintToRank.length) {
				// the even ranks are already all unassigned (FIXME: don't understand this comment)
				// no chance for rk+1
				// we have to give them the odd rk-1
				// and finish afterwards
				lrwsi.addOddRanks(constraintToRank, rk-1);
				addResult(lrwsi.assignRestictedAndgetLevelRankingState());
				return;
			}
			
			
			/*
			 * Unrestricted DDs that we have to assign to rk+1 because our
			 * constraints do not allow a higher rank.
			 */
			final DoubleDecker<StateWithRankInfo<STATE>>[] constraintToRankPlusOne = getUnrestrictedWithMaxRank(rk+1);
			
			if (lrwsi.numberUnsatisfiedLowerRanks() + 1 > unassignedUnrestricted) {
				throw new AssertionError("unable to assign all ranks");
			}
			
			List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
			/**
			 * States for which we definitely construct a copy in which they
			 * give up their even rank for the lower odd rank.
			 */
			List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantLeave = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
			/**
			 * States for which we only construct a copy in which their rank
			 * is reduced if this helps another state to obtain a high odd rank
			 * in a tight level ranking.
			 */
			List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankInO_WantStay = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
			List<DoubleDecker<StateWithRankInfo<STATE>>> constraintToRankNotInO = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
			for (DoubleDecker<StateWithRankInfo<STATE>> dd : constraintToRank) {
				if (super.m_Constraint.inO(dd.getDown(), dd.getUp().getState())) {
					if (m_SuccessorsOfFinalsWantToLeaveO  && 
							super.m_Constraint.getPredecessorWasAccepting().contains(dd)) {
						constraintToRankInO_WantLeave.add(dd);
					} else {
						constraintToRankInO_WantStay.add(dd);
					}
					constraintToRankInO.add(dd);
				} else {
					constraintToRankNotInO.add(dd);
				}
				
			}
			
			// number of copies that we need in this iteration
			final int numberOfCopies;
			if (rk > 0) {
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
			 * candidates for the even rank rk, the odd rank rk-1 instead.
			 * E.g., two DoubleDeckerWithRankInfos in this example.
			 */
			
			// number of odd ranks that we have to assign with even-candidates 
			// in order to be able to assign the odd rank rk+1 
			final int numberOfOddRanksThatWeHaveToAssignAdditionally = lrwsi.numberUnsatisfiedLowerRanks() + 1 - (unassignedUnrestricted - constraintToRank.length);
			final int unassignedUnrestrictedAfterThisTurn = unassignedUnrestricted - constraintToRank.length - constraintToRankPlusOne.length;
			final int assignedUnrestrictedAfterThisTurn = assignedUnrestricted + constraintToRank.length + constraintToRankPlusOne.length;
			
			int surplus = surplus(rk);
			surplus = surplus(rk);
			final int maxNumberOfEvenRanksWeMayAssign = unassignedUnrestricted -( lrwsi.numberUnsatisfiedLowerRanks() + 1);
			final int surplusRk = surplus(rk);
			final int netSurplus = surplusRk - lrwsi.numberUnsatisfiedLowerRanks();
			final int numberOfOddRankTheWeCouldAssignAdditionally = Math.max(lrwsi.numberUnsatisfiedLowerRanks() - surplusRk, 0);
			if (numberOfOddRankTheWeCouldAssignAdditionally > 1 && numberOfCopies > 1) {
				m_Logger.info("Sacrifice!");
			}

//			assert constraintToRank.length - maxNumberOfEvenRanksWeMayAssign == numberOfOddRanksThatWeHaveToAssignAdditionally;
			
			
			int inOmultiplier = (int) Math.pow(2, constraintToRankInO.size());
			int notInOmultiplier = (int) Math.pow(2, constraintToRankNotInO.size());
			assert (numberOfCopies == inOmultiplier * notInOmultiplier);
			for (int i=0; i<inOmultiplier; i++) {
				int bitcount_i = Integer.bitCount(i);
				if (bitcount_i + constraintToRankNotInO.size() < numberOfOddRanksThatWeHaveToAssignAdditionally) {
					// we give up this branch, we can not achieve that each
					// odd rank is assigned once.
					continue;
				}
				for (int j=0; j<notInOmultiplier; j++) {
					int bitcount_j = Integer.bitCount(j);
					if (bitcount_i + bitcount_j < numberOfOddRanksThatWeHaveToAssignAdditionally) {
						// we give up this branch, we can not achieve that each
						// odd rank is assigned once.
						continue;
					}
					if ((bitcount_i + bitcount_j > numberOfOddRankTheWeCouldAssignAdditionally)) {
						// we give up this branch, sacrificing that many even
						// ranks wont' bring us a higher maximal rank
						continue;
					}
					LevelRankingWithSacrificeInformation copy = new LevelRankingWithSacrificeInformation(lrwsi);
					for (int k=0; k<constraintToRankInO.size(); k++) {
						if (BigInteger.valueOf(i).testBit(k)) {
							copy.addOddRank(constraintToRankInO.get(k), rk-1, true);
						}
					}
					for (int k=0; k<constraintToRankNotInO.size(); k++) {
						if (BigInteger.valueOf(j).testBit(k)) {
							copy.addOddRank(constraintToRankNotInO.get(k), rk-1, true);
						}
					}
					copy.increaseCurrentRank();
					assert copy.m_CurrentRank == rk;
					int evenRanksAssignedSoFar = 0;
					for (int k=0; k<constraintToRankInO.size(); k++) {
						if (!BigInteger.valueOf(i).testBit(k)) {
							copy.addEvenRank(constraintToRankInO.get(k), rk);
							evenRanksAssignedSoFar++;
						}
					}
					for (int k=0; k<constraintToRankNotInO.size(); k++) {
						if (!BigInteger.valueOf(j).testBit(k)) {
							copy.addEvenRank(constraintToRankNotInO.get(k), rk);
							evenRanksAssignedSoFar++;
						}
					}
					assert (evenRanksAssignedSoFar <= maxNumberOfEvenRanksWeMayAssign);
					copy.increaseCurrentRank();
					copy.addOddRanks(constraintToRankPlusOne, rk+1);
					int numberUnassignedLowerRanks = copy.numberUnsatisfiedLowerRanks();
					if (unassignedUnrestrictedAfterThisTurn == numberUnassignedLowerRanks) {
						copy.assignRemainingUnrestricted(rk+1, unassignedUnrestrictedAfterThisTurn);
						addResult(copy.assignRestictedAndgetLevelRankingState());
						continue;
					} else {
						recursivelyComputeResults(rk+2, copy, assignedUnrestrictedAfterThisTurn, unassignedUnrestrictedAfterThisTurn);
						continue;
					}
				}
			}
			return;
		}
		
		/**
		 * If we assign ranks starting from the highest down to i such that we
		 * given even ranks for even bounds, how many ranks do we have as 
		 * surplus that we can use to satisfy odd ranks < i without having
		 * DoubleDeckerWithRankInfos for this rank.
		 * E.g.,
		 * for the ranks 5 3 1, the surplus for i = 3 is 0
		 * for the ranks 3 3 1, the surplus for i = 3 is 1
		 * for the ranks 3 2 1, the surplus for i = 3 is 0
		 * for the ranks 4 3 1, the surplus for i = 3 is 1
		 * for the ranks ∞ ∞ 3, the surplus for i = 3 is 0
		 * for the ranks ∞ ∞ 3, 3 the surplus for i = 3 is 1
		 * for the ranks ∞ ∞ 4, 3 the surplus for i = 3 is 0
		 * for the ranks 11 9 5 5 3 the surplus for i = 3 is 1
		 * 
		 */
		private int surplus(int i) {
			int unbounded = m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.numberofPairsWithGivenDomainElement(Integer.MAX_VALUE);
			final int highestBound;
			{
				Iterator<Integer> it = m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.descendingDomain().iterator();
				assert it.hasNext();
				Integer first = it.next();
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
			int rank;
			int surplus;
			if (isEven(highestBound)) {
				// if rank is even
				// if there some with ∞-bound these even rank do not contribute
				// to the surplus
				// if there no with ∞-bound all these have to take the next odd
				// rank
				if (unbounded > 0) {
					surplus = 0;
				} else {
					surplus = m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.numberofPairsWithGivenDomainElement(highestBound);
				}
				rank = highestBound - 1;
			} else {
				surplus = 0;
				rank = highestBound;
			}
			while (rank >= i) {
				assert isOdd(rank);
				int ddWithRank = m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.numberofPairsWithGivenDomainElement(rank);
				surplus += (ddWithRank - 1);
				if (surplus < 0) {
					assert surplus == -1;
					surplus = 0;
				}
				rank -= 2;
			}
			return surplus;
		}		
		
		
		private class LevelRankingWithSacrificeInformation {
			private final LevelRankingState<LETTER,STATE> m_Lrs;
			private int m_CurrentRank = -1;
			/**
			 * Number of odd ranks rk such that the number of DoubleDeckerWithRankInfos that 
			 * have an odd rank i >= rk is smaller than or equal to 
			 * (m_CurrentRank - rk + 1). 
			 */
			private final TreeSet<Integer> m_UnSatisfiedOddRanks;
//			private final Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> m_Sacrificable;
			/**
			 * DoubleDeckerWithRankInfos that we assigned the odd rank rk although its
			 * constraints would have allows the even rank rk+1.
			 */
			private final List<DoubleDecker<StateWithRankInfo<STATE>>> m_SacrificedDoubleDeckerWithRankInfos;
			
			LevelRankingWithSacrificeInformation() {
				m_Lrs = new LevelRankingState<LETTER,STATE>(m_Operand);
				m_UnSatisfiedOddRanks = new TreeSet<Integer>();
				m_SacrificedDoubleDeckerWithRankInfos = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
//				m_Sacrificable = new HashMap<DoubleDecker<StateWithRankInfo<STATE>>, Integer>();
			}
			
			int numberUnsatisfiedLowerRanks() {
				return m_UnSatisfiedOddRanks.size();
			}
			
			void increaseCurrentRank() {
				m_CurrentRank++;
				if (m_CurrentRank % 2 == 1) {
					m_UnSatisfiedOddRanks.add(m_CurrentRank);
				}
			}
			
			void addOddRank(DoubleDecker<StateWithRankInfo<STATE>> dd, int rank, boolean isSacrifice) {
				assert rank % 2 == 1;
				assert rank == m_CurrentRank;
				boolean addToO = false;
				m_Lrs.addRank(dd.getDown(), dd.getUp().getState(), rank, addToO);
				Integer removed = m_UnSatisfiedOddRanks.pollLast();
				if (isSacrifice) {
					m_SacrificedDoubleDeckerWithRankInfos.add(dd);
				}
//				if (removed != null) {
//					updateSacrificable(removed);
//				}
			}
			void addOddRanks(DoubleDecker<StateWithRankInfo<STATE>>[] dds, int rank) {
				for (DoubleDecker<StateWithRankInfo<STATE>> dd : dds) {
					addOddRank(dd, rank, false);
				}
			}
			
//			private void updateSacrificable(Integer removed) {
//				Iterator<Entry<DoubleDecker<StateWithRankInfo<STATE>>, Integer>> it = 
//						m_Sacrificable.entrySet().iterator();
//				while (it.hasNext()) {
//					Entry<DoubleDecker<StateWithRankInfo<STATE>>, Integer> entry = it.next();
//					if (entry.getValue().equals(removed)) {
//						Integer nextHighest = m_UnassignedOddRanks.floor(removed);
//						if (nextHighest == null) {
//							it.remove();
//						} else {
//							entry.setValue(nextHighest);
//						}
//					}
//				}
//			}

			void addEvenRank(DoubleDecker<StateWithRankInfo<STATE>> dd, int rank) {
				assert rank % 2 == 0;
				assert rank == m_CurrentRank;
				boolean addToO = HeiMatTightLevelRankingStateGenerator.super
						.m_Constraint.inO(dd.getDown(), dd.getUp().getState());
				m_Lrs.addRank(dd.getDown(), dd.getUp().getState(), rank, addToO);
				if (!m_UnSatisfiedOddRanks.isEmpty()) {
					Integer highestUnassigned = m_UnSatisfiedOddRanks.last();
					assert (highestUnassigned < rank);
//					m_Sacrificable.put(dd, highestUnassigned);
				}
			}
			
			public LevelRankingState<LETTER,STATE> assignRestictedAndgetLevelRankingState() {
				if (!m_UnSatisfiedOddRanks.isEmpty()) {
					throw new AssertionError("not all odd ranks assigned yet");
				}
				assert m_Lrs.m_HighestRank % 2 == 1 : "maxrank is always odd";
				for (DoubleDecker<StateWithRankInfo<STATE>> dd  : HeiMatTightLevelRankingStateGenerator.super.m_RestrictedDoubleDeckerWithRankInfo) {
					Integer rank;
					boolean inO = HeiMatTightLevelRankingStateGenerator.super.m_Constraint.inO(dd.getDown(), dd.getUp().getState());
					if (HeiMatTightLevelRankingStateGenerator.super.m_Constraint.getRank(dd.getDown(), dd.getUp().getState()) <= m_Lrs.m_HighestRank) {
						int bound = HeiMatTightLevelRankingStateGenerator.super.m_Constraint.getRank(dd.getDown(), dd.getUp().getState());
						if (bound % 2 == 0) {
							rank = bound;
						} else {
							rank = bound -1;
						}
					} else {
						if (m_SacrificedDoubleDeckerWithRankInfos.size() > 1) {
							m_Logger.warn("unneccessary sacrifice !!! this state is is not needed, "
									+ "construction can be optimized, contact Matthias");
						}
						rank = m_Lrs.m_HighestRank - 1;
					}
					m_Lrs.addRank(dd.getDown(), dd.getUp().getState(), rank, inO);
				}
				return m_Lrs;
			}
			
			public LevelRankingWithSacrificeInformation(LevelRankingWithSacrificeInformation copy) {
				this.m_Lrs = new LevelRankingState<LETTER,STATE>(copy.m_Lrs);
				m_CurrentRank = copy.m_CurrentRank;
				m_UnSatisfiedOddRanks = new TreeSet<Integer>(copy.m_UnSatisfiedOddRanks);
				m_SacrificedDoubleDeckerWithRankInfos = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>(copy.m_SacrificedDoubleDeckerWithRankInfos);
//				m_Sacrificable = new HashMap<DoubleDecker<StateWithRankInfo<STATE>>, Integer>(copy.m_Sacrificable);
			}
			
			
			void assignRemainingUnrestricted(Integer rank,
					int unassignedUnrestricted) {
				assert rank == m_CurrentRank;
				assert unassignedUnrestricted >= m_UnSatisfiedOddRanks.size();
				HeiMatTightLevelRankingStateGenerator.this.assignRemainingUnrestricted(rank, m_Lrs, unassignedUnrestricted);
				m_UnSatisfiedOddRanks.clear();
			}
			
		}



		private void addResult(LevelRankingState<LETTER,STATE> lrs) {
			assert lrs.m_LevelRanking.size() == super.m_Constraint.m_LevelRanking.size();
			m_Result.add(lrs);
						
		}

		private void assignRemainingUnrestricted(Integer rank,
				LevelRankingState<LETTER,STATE> lrs,  int unassignedUnrestricted) {
			assert rank % 2 == 1 : "maxrank is always odd";
			Integer noRankBound = Integer.MAX_VALUE;
			if (m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.getDomain().contains(noRankBound)) {
				for (DoubleDecker<StateWithRankInfo<STATE>> dd : m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.getImage(noRankBound)) {
					lrs.addRank(dd.getDown(), dd.getUp().getState(), rank, false);
					unassignedUnrestricted--;
				}
			}
			assert unassignedUnrestricted >= 0;
			int rankBound = rank + 1;
			while (unassignedUnrestricted > 0) {
				if (m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.getDomain().contains(rankBound)) {
					for (DoubleDecker<StateWithRankInfo<STATE>> dd : m_UnrestrictedMaxRank2DoubleDeckerWithRankInfo.getImage(rankBound)) {
						lrs.addRank(dd.getDown(), dd.getUp().getState(), rank, false);
						unassignedUnrestricted--;
					}
				}
				rankBound++;
				if (rankBound > 1000) {
					throw new AssertionError("forgotten rank bound?, there are no automata with rank > 1000 in the nature");
				}
			}
		}
		
		



		@Override
		public String toString() {
			return super.m_Constraint.toString() + " Unrestricted: " 
					+ super.m_UnrestrictedDoubleDeckerWithRankInfo;
		}
		
		
		
	}
	
	
	/**
	 * Use this together with MaxTightLevelRankingStateGeneratorNonInitial.
	 * The MaxTightLevelRankingStateGeneratorInitial should generate the 
	 * LevelRankings for successors of determinized states (from powerset
	 * construction) the MaxTightLevelRankingStateGeneratorNonInitial should
	 * generate other LevelRankings.
	 * I tried to implement the optimization suggested in Section 4 of
	 * 2009STACS - Schewe - Büchi Complementation Made Tight
	 * This is still buggy and meanwhile I think that my optimization is more 
	 * efficient.
	 *
	 */
	private class MaxTightLevelRankingStateGeneratorInitial extends
											TightLevelRankingStateGenerator {
		final List<DoubleDecker<StateWithRankInfo<STATE>>> m_FinalDoubleDeckerWithRankInfos = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();
		final List<DoubleDecker<StateWithRankInfo<STATE>>> m_NonFinalDoubleDeckerWithRankInfos = new ArrayList<DoubleDecker<StateWithRankInfo<STATE>>>();

		public MaxTightLevelRankingStateGeneratorInitial(
				LevelRankingConstraint<LETTER,STATE> constraint) {
			super(constraint);
			for (StateWithRankInfo<STATE> down  : constraint.getDownStates()) {
				for (StateWithRankInfo<STATE> up : constraint.getUpStates(down)) {
					assert up.getRank() == Integer.MAX_VALUE;
					DoubleDecker<StateWithRankInfo<STATE>> dd = new DoubleDecker<StateWithRankInfo<STATE>>(down, up);
					if (m_Operand.isFinal(up.getState())) {
						m_FinalDoubleDeckerWithRankInfos.add(dd);
					} else {
						m_NonFinalDoubleDeckerWithRankInfos.add(dd);
					}
				}
			}

		}
		
		public void rec(int rank, Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assigned) {
			if (assigned.size() == m_NonFinalDoubleDeckerWithRankInfos.size()) {
				int maxrank = rank - 2;
				int highestEvenRank = maxrank - 1;
				LevelRankingState<LETTER,STATE> lrs = new LevelRankingState<LETTER,STATE>(m_Operand);
				for (DoubleDecker<StateWithRankInfo<STATE>> dd : assigned.keySet()) {
					lrs.addRank(dd.getDown(), dd.getUp().getState(), assigned.get(dd), false);
				}
				for (DoubleDecker<StateWithRankInfo<STATE>> dd : m_FinalDoubleDeckerWithRankInfos) {
					lrs.addRank(dd.getDown(), dd.getUp().getState(), highestEvenRank, true);
				}
				m_Result.add(lrs);
			} else {
				for (DoubleDecker<StateWithRankInfo<STATE>> dd  : m_NonFinalDoubleDeckerWithRankInfos) {
					if (!assigned.containsKey(dd)) {
						Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> assignedCopy = 
								new HashMap<DoubleDecker<StateWithRankInfo<STATE>>, Integer>(assigned);
						assignedCopy.put(dd, rank);
						rec(rank + 2, assignedCopy);
					}
				}
			}
		}

		@Override
		Collection<LevelRankingState<LETTER,STATE>> computeResult() {
			if (m_NonFinalDoubleDeckerWithRankInfos.size() != 0) {
				Map<DoubleDecker<StateWithRankInfo<STATE>>, Integer> empty = Collections.emptyMap();
				rec(1, empty);
			}
			return m_Result;
		}
		
	}
	
	
	/**
	 * Use this together with MaxTightLevelRankingStateGeneratorInitial.
	 */
	private class MaxTightLevelRankingStateGeneratorNonInitial extends TightLevelRankingStateGenerator {

		public MaxTightLevelRankingStateGeneratorNonInitial(
				LevelRankingConstraint<LETTER,STATE> constraint) {
			super(constraint);
		}

		@Override
		Collection<LevelRankingState<LETTER,STATE>> computeResult() {
			if (m_Constraint.getDownStates().isEmpty()) {
				return Collections.emptySet();
			}
			if (m_Constraint.isTight()) {
				LevelRankingState<LETTER,STATE> pointwiseMax = new LevelRankingState<LETTER,STATE>(m_Operand);
				for (StateWithRankInfo<STATE> down  : m_Constraint.getDownStates()) {
					for (StateWithRankInfo<STATE> up : m_Constraint.getUpStates(down)) {
						int rank = up.getRank();
						if (m_Operand.isFinal(up.getState()) && isOdd(rank)) {
							rank--;
						}
						if (up.isInO() && isEven(rank)) {
							pointwiseMax.addRank(down, up.getState(), rank, true);
						} else {
							pointwiseMax.addRank(down, up.getState(), rank, false);
						}
					}
				}
				m_Result.add(pointwiseMax);
				if (!pointwiseMax.isOempty()) {
					LevelRankingState<LETTER,STATE> lrs = new LevelRankingState<LETTER,STATE>(m_Operand);
					for (StateWithRankInfo<STATE> down  : pointwiseMax.getDownStates()) {
						for (StateWithRankInfo<STATE> up : pointwiseMax.getUpStates(down)) {
							int rank = up.getRank();
							if (up.isInO()) {
								if (rank == 0 || m_Operand.isFinal(up.getState())) {
									lrs.addRank(down, up.getState(), rank, true);
								} else {
									lrs.addRank(down, up.getState(), rank-1, false);
								}
							} else {
								lrs.addRank(down, up.getState(), rank, false);
							}
						}
					}
					if (!lrs.equals(pointwiseMax)) {
						m_Result.add(lrs);
					}
				}
			}
			return m_Result;
		}
	}
	



	public static boolean isOdd(int i) {
		if (i >= 0) {
			return i % 2 == 1;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	public static boolean isEven(int i) {
		if (i >= 0) {
			return i % 2 == 0;
		} else {
			throw new IllegalArgumentException();
		}
	}




}
