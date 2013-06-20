package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.plaf.basic.BasicInternalFrameTitlePane.MaximizeAction;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IDeterminizedState;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKVNwa<LETTER,STATE> implements INestedWordAutomatonSimple<LETTER,STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is suffient, see paper of Seth Forgaty.
	 */
	private final int m_UserDefinedMaxRank = Integer.MAX_VALUE;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	
	private final NestedWordAutomatonCache<LETTER, STATE> m_Cache;
	
	StateFactory<STATE> m_StateFactory;
	
	/**
	 * Maps DeterminizedState to its representative in the resulting automaton.
	 */
	private final Map<DeterminizedState<LETTER,STATE>,STATE> m_det2res =
		new HashMap<DeterminizedState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the DeterminizedState for which it
	 * was created.
	 */
	private final Map<STATE,DeterminizedState<LETTER,STATE>> m_res2det =
		new HashMap<STATE, DeterminizedState<LETTER,STATE>>();
	
	/**
	 * Maps a LevelRankingState to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState,STATE> m_lrk2res =
		new HashMap<LevelRankingState, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the LevelRankingState for which it
	 * was created.
	 */
	private final Map<STATE,LevelRankingState> m_res2lrk =
		new HashMap<STATE, LevelRankingState>();
	
	private final IStateDeterminizer<LETTER,STATE> m_StateDeterminizer;
	
	/**
	 * Highest rank that occured during the construction. Used only for
	 *  statistics.
	 */
	int m_HighestRank = -1;	
	
	
	
	
	public BuchiComplementFKVNwa(INestedWordAutomatonSimple<LETTER,STATE> operand,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			StateFactory<STATE> stateFactory) throws OperationCanceledException {
		m_Operand = operand;
		m_StateFactory = stateFactory;
		m_Cache = new NestedWordAutomatonCache<LETTER, STATE>(
				operand.getInternalAlphabet(), operand.getCallAlphabet(), 
				operand.getReturnAlphabet(), m_StateFactory);
		m_StateDeterminizer = stateDeterminizer;
	}
	
	
	private void constructInitialState() {
		DeterminizedState<LETTER,STATE> detState = m_StateDeterminizer.initialState();
		getOrAdd(detState, true);	
	}
	

	/**
	 * Return state of result automaton that represents lrkState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(LevelRankingState lrkState) {
		STATE resSucc = m_lrk2res.get(lrkState);
		if (resSucc == null) {
			resSucc = lrkState.getContent();
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
	private STATE getOrAdd(DeterminizedState<LETTER,STATE> detState, boolean isInitial) {
		STATE resSucc = m_det2res.get(detState);
		if (resSucc == null) {
			resSucc = detState.getContent(m_StateFactory);
			assert resSucc != null;
			m_Cache.addState(isInitial, false, resSucc);
			m_det2res.put(detState, resSucc);
			m_res2det.put(resSucc, detState);
		}
		return resSucc;
	}
	
	public int getHighesRank() {
		return m_HighestRank;
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
			DeterminizedState<LETTER,STATE> detUp = m_res2det.get(state);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = 
						m_StateDeterminizer.internalSuccessor(detUp, letter);
					if (!detSucc.isEmpty()) {
						STATE resSucc = getOrAdd(detSucc, false);
						m_Cache.addInternalTransition(state, letter, resSucc);
						resSuccs.add(resSucc);
					}
				}
				LevelRankingConstraint constraints = new LevelRankingConstraint();
				constraints.internalSuccessorConstraints(detUp, letter);
				TightLevelRankingStateGenerator gen = 
					new MatthiasTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState> result = gen.computeResult();
				for (LevelRankingState complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState complUp = m_res2lrk.get(state);
			if (complUp != null) {
				LevelRankingConstraint constraints = new LevelRankingConstraint();
				constraints.internalSuccessorConstraints(complUp, letter);
				MatthiasTightLevelRankingStateGenerator gen = 
					new MatthiasTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState> result = gen.computeResult();
				for (LevelRankingState complSucc : result) {
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
			DeterminizedState<LETTER,STATE> detUp = m_res2det.get(state);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = 
						m_StateDeterminizer.callSuccessor(detUp, letter);
					if (!detSucc.isEmpty()) {
						STATE resSucc = getOrAdd(detSucc, false);
						m_Cache.addCallTransition(state, letter, resSucc);
						resSuccs.add(resSucc);
					}
				}
				LevelRankingConstraint constraints = new LevelRankingConstraint();
				constraints.callSuccessorConstraints(detUp, letter);
				TightLevelRankingStateGenerator gen = 
					new MatthiasTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState> result = gen.computeResult();
				for (LevelRankingState complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState complUp = m_res2lrk.get(state);
			if (complUp != null) {
				LevelRankingConstraint constraints = new LevelRankingConstraint();
				constraints.callSuccessorConstraints(complUp, letter);
				MatthiasTightLevelRankingStateGenerator gen = 
					new MatthiasTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState> result = gen.computeResult();
				for (LevelRankingState complSucc : result) {
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
			DeterminizedState<LETTER,STATE> detUp = m_res2det.get(state);
			DeterminizedState<LETTER,STATE> detDown = m_res2det.get(hier);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = 
						m_StateDeterminizer.returnSuccessor(detUp, detDown, letter);
					if (!detSucc.isEmpty()) {
						STATE resSucc = getOrAdd(detSucc, false);
						m_Cache.addReturnTransition(state, hier, letter, resSucc);
						resSuccs.add(resSucc);
					}
				}
				LevelRankingConstraint constraints = new LevelRankingConstraint();
				constraints.returnSuccessorConstraints(detUp, detDown, letter);
				TightLevelRankingStateGenerator gen = 
					new MatthiasTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState> result = gen.computeResult();
				for (LevelRankingState complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState complUp = m_res2lrk.get(state);
			IDeterminizedState<LETTER, STATE> complDown;
			if (m_res2det.containsKey(hier)) {
				complDown = m_res2det.get(hier);
			} else {
				assert m_res2lrk.containsKey(hier);
				complDown = m_res2lrk.get(hier);
			}
			if (complUp != null) {
				LevelRankingConstraint constraints = new LevelRankingConstraint();
				constraints.returnSuccessorConstraints(complUp, complDown, letter);
				MatthiasTightLevelRankingStateGenerator gen = 
					new MatthiasTightLevelRankingStateGenerator(constraints);
				Collection<LevelRankingState> result = gen.computeResult();
				for (LevelRankingState complSucc : result) {
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
	public boolean accepts(Word<LETTER> word) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}
	
	
	
	
	
	
	
	
	
	/**
	 * Represents a state (S,O,g) in the complement automaton.
	 * <ul>
	 *   <li> The level ranking g is modelled by m_LevelRanking
	 *   <li> The set O is modelled by m_O
	 *   <li> The set S contains all DoubleDecker for which m_LevelRanking is
	 *   defined 
	 * </ul> 
	 * TODO Encode O in m_LevelRanking. E.g. map DoubleDecker in O instead of
	 * its rank to rank-1000.
	 */
	public class LevelRankingState implements IDeterminizedState<LETTER, STATE> {
		Map<STATE,HashMap<STATE,Integer>> m_LevelRanking = 
						new HashMap<STATE,HashMap<STATE,Integer>>();
		
		Map<STATE,Set<STATE>> m_O = 
						new HashMap<STATE,Set<STATE>>();
		
		/**
		 * Highest rank in this LevelRankingState. Only used to get statistics.
		 */
		int m_HighestRank = -1;
		
		public Set<STATE> getDownStates() {
			return m_LevelRanking.keySet();
		}
		
		public Set<STATE> getUpStates(STATE downState) {
			return m_LevelRanking.get(downState).keySet();
		}
		
		private void addRank(STATE down, STATE up, 
												Integer rank, boolean addToO) {
			assert rank != null;
			HashMap<STATE, Integer> up2rank = m_LevelRanking.get(down);
			if (up2rank == null) {
				up2rank = new HashMap<STATE,Integer>();
				m_LevelRanking.put(down, up2rank);
			}
			assert !up2rank.containsKey(up);
			up2rank.put(up,rank);
			if (addToO) {
				addToO(down,up);
			}
			if (m_HighestRank < rank) {
				m_HighestRank = rank;
			}
		}
		
		protected void addToO(STATE down, STATE up) {
			Set<STATE> upStates = m_O.get(down);
			if (upStates == null) {
				upStates = new HashSet<STATE>();
				m_O.put(down, upStates);
			}
			upStates.add(up);
		}
		
		public Integer getRank(STATE down, STATE up) {
			HashMap<STATE, Integer> up2rank = m_LevelRanking.get(down);
			if (up2rank == null) {
				return null;
			}
			else {
				return up2rank.get(up);
			}
		}
		
		public boolean inO(STATE down, STATE up) {
			Set<STATE> upStates = m_O.get(down);
			if (upStates == null) {
				return false;
			}
			return upStates.contains(up);
		}
		
		boolean isOempty() {
			return m_O.isEmpty();
		}
		
		STATE getContent() {
			assert !m_LevelRanking.isEmpty();
			return m_StateFactory.buchiComplementFKV((LevelRankingState) this);
		}
		
		@Override
		public String toString() {
			return m_LevelRanking.toString() +" O"+m_O;
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#hashCode()
		 */
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime
					* result
					+ ((m_LevelRanking == null) ? 0 : m_LevelRanking.hashCode());
			result = prime * result + ((m_O == null) ? 0 : m_O.hashCode());
			return result;
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			LevelRankingState other = (LevelRankingState) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (m_LevelRanking == null) {
				if (other.m_LevelRanking != null)
					return false;
			} else if (!m_LevelRanking.equals(other.m_LevelRanking))
				return false;
			if (m_O == null) {
				if (other.m_O != null)
					return false;
			} else if (!m_O.equals(other.m_O))
				return false;
			return true;
		}
		private BuchiComplementFKVNwa<LETTER,STATE> getOuterType() {
			return BuchiComplementFKVNwa.this;
		}
	}
	
	
	
	/**
	 * Constraints that define a set of LevelRankingStates.
	 * <ul>
	 * <li> m_LevelRanking represents an upper bound for ranks of 
	 * LevelRankingStates defined by this LevelRankingConstraints.
	 * <li> A DoubleDecker is in LevelRankingState.m_O iff (it is in 
	 *   LevelRankingConstraints.m_O and it has an even level rank)
	 * </ul>
	 */
	public class LevelRankingConstraint extends LevelRankingState {
		
		void internalSuccessorConstraints(IDeterminizedState<LETTER, STATE> state, LETTER symbol) {
			for (STATE down : state.getDownStates()) {
				for (STATE up : state.getUpStates(down)) {
					boolean oCandidate;
					Integer upRank;
					if (state instanceof BuchiComplementFKVNwa.LevelRankingState) {
						LevelRankingState lvlRkState = (LevelRankingState) state;
						oCandidate = lvlRkState.isOempty() || lvlRkState.inO(down,up);
						upRank = lvlRkState.getRank(down, up);
					} else {
						oCandidate = false;
						upRank = Integer.MAX_VALUE;
					}
					for (OutgoingInternalTransition<LETTER, STATE> trans : 
									m_Operand.internalSuccessors(up,symbol)) {
						addConstaint(down, trans.getSucc(), upRank, oCandidate);
					}
				}
			}
		}
		
		void callSuccessorConstraints(IDeterminizedState<LETTER, STATE> state, LETTER symbol) {
			for (STATE down : state.getDownStates()) {
				for (STATE up : state.getUpStates(down)) {
					boolean oCandidate;
					Integer upRank;
					if (state instanceof BuchiComplementFKVNwa.LevelRankingState) {
						LevelRankingState lvlRkState = (LevelRankingState) state;
						oCandidate = lvlRkState.isOempty() || lvlRkState.inO(down,up);
						upRank = lvlRkState.getRank(down, up);
					} else {
						oCandidate = false;
						upRank = Integer.MAX_VALUE;
					}
					for (OutgoingCallTransition<LETTER, STATE> trans : 
									m_Operand.callSuccessors(up,symbol)) {
						STATE succDownState;
						// if !m_UseDoubleDeckers we always use getEmptyStackState()
						// as down state to obtain sets of states instead of
						// sets of DoubleDeckers.
						if (m_StateDeterminizer.useDoubleDeckers()) {
							succDownState = up;
						} else {
							succDownState = m_Operand.getEmptyStackState();
						}
						addConstaint(succDownState, trans.getSucc(), upRank, oCandidate);
					}
				}
			}
		}
		
		void returnSuccessorConstraints(IDeterminizedState<LETTER, STATE> state, 
				IDeterminizedState<LETTER, STATE> hier, LETTER symbol) {
			for (STATE hierDown : hier.getDownStates()) {
				for (STATE hierUp : hier.getUpStates(hierDown)) {
					if (state.getDownStates().isEmpty()) {
						continue;
						//throw new AssertionError();
					}
					STATE downState;
					if (m_StateDeterminizer.useDoubleDeckers()) {
						if (!state.getDownStates().contains(hierUp)) {
							continue;
						}
						downState = hierUp;
					} else {
						assert state.getDownStates().size() == 1;
						assert state.getDownStates().iterator().next() == 
												m_Operand.getEmptyStackState();
						// if !m_UseDoubleDeckers we always use getEmptyStackState()
						// as down state to obtain sets of states instead of
						// sets of DoubleDeckers.
						downState = m_Operand.getEmptyStackState();

					}
					Set<STATE> upStates = state.getUpStates(downState);
					addReturnSuccessorConstraintsGivenDownState(state,
							downState, upStates, hierDown, hierUp, symbol);
				}
			}
		}

		private void addReturnSuccessorConstraintsGivenDownState(
				IDeterminizedState<LETTER, STATE> state, STATE downState, Set<STATE> upStates,
				STATE hierDown, STATE hierUp, LETTER symbol) {
			for (STATE stateUp : upStates) {
				boolean oCandidate;
				Integer upRank;
				if (state instanceof BuchiComplementFKVNwa.LevelRankingState) {
					LevelRankingState lvlRkState = (LevelRankingState) state;
					oCandidate = lvlRkState.isOempty() || lvlRkState.inO(downState,stateUp);
					upRank = lvlRkState.getRank(downState, stateUp);
				} else {
					oCandidate = false;
					upRank = Integer.MAX_VALUE;
				}
				for (OutgoingReturnTransition<LETTER, STATE> trans : 
								m_Operand.returnSucccessors(stateUp,hierUp,symbol)) {
					assert m_StateDeterminizer.useDoubleDeckers() || hierDown == m_Operand.getEmptyStackState();
					addConstaint(hierDown, trans.getSucc(), upRank, oCandidate);
				}
			}
		}

		

		

		private void addConstaint(STATE down, STATE up, 
											Integer rank, boolean oCandidate) {
			HashMap<STATE, Integer> up2rank = m_LevelRanking.get(down);
			if (up2rank == null) {
				up2rank = new HashMap<STATE,Integer>();
				m_LevelRanking.put(down, up2rank);
			}
			Integer oldRank = up2rank.get(up);
			if (oldRank == null || oldRank > rank) {
				up2rank.put(up,rank);
			}
			if (oCandidate) {
				addToO(down,up);
			}
		}		
	}

	
	

	
	/**
	 * Generates all LevelRanking states that are tight (see 2004ATVA paper)
	 * and fulfill given LevelRankingConstraints.
	 */
	public class TightLevelRankingStateGenerator {

		private final List<DoubleDecker<STATE>> m_UnrestrictedDoubleDecker = 
			new ArrayList<DoubleDecker<STATE>>();
		private final List<Integer> m_UnrestrictedMaxRank = 
			new ArrayList<Integer>();
		protected int[] m_UnrestrictedRank;
		
		private final List<DoubleDecker<STATE>> m_RestrictedDoubleDecker = 
			new ArrayList<DoubleDecker<STATE>>();
		protected final List<Integer> m_RestrictedMaxRank = 
			new ArrayList<Integer>();
		protected int[] m_RestrictedRank;
		
		private final List<LevelRankingState> m_Result =
			new ArrayList<LevelRankingState>();
		private final LevelRankingConstraint m_Constraint;
		
		public TightLevelRankingStateGenerator(LevelRankingConstraint constraint) {
			m_Constraint = constraint;
		}
		
		// Idea behind this construction. Partition DoubleDecker into Restricted
		// and Unrestricted.
		// A double Decker is restricted iff is has to have an even rank in
		// each LevelRankingState defined by this LevelRankingConstraint.
		//
		Collection<LevelRankingState> computeResult() {
			for (STATE down : m_Constraint.getDownStates()) {
				for (STATE up : m_Constraint.getUpStates(down)) {
					Integer rank = m_Constraint.getRank(down, up);
					if (m_Operand.isFinal(up) || rank == 0) {
						m_RestrictedDoubleDecker.add(
											new DoubleDecker<STATE>(down, up));
						m_RestrictedMaxRank.add(rank);
					}
					else {
						m_UnrestrictedDoubleDecker.add(
											new DoubleDecker<STATE>(down, up));
						m_UnrestrictedMaxRank.add(rank);
					}
				}
			}
			
			m_UnrestrictedRank = new int[m_UnrestrictedMaxRank.size()];
			m_RestrictedRank = new int[m_RestrictedMaxRank.size()];
			
//			s_Logger.debug("Constructing LevelRankings for" + 
//									m_UnrestrictedDoubleDecker.toString() + 
//									m_RestrictedDoubleDecker.toString());
			
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
		
		private void constructComplementState() {
//			s_Logger.debug("Rank " + Arrays.toString(m_UnrestrictedRank) + 
//											Arrays.toString(m_RestrictedRank));
			LevelRankingState result = new LevelRankingState();
			for (int i=0; i<m_RestrictedRank.length; i++) {
				DoubleDecker<STATE> dd = m_RestrictedDoubleDecker.get(i);
				STATE down = dd.getDown();
				STATE up = dd.getUp();
				int rank = m_RestrictedRank[i];
				boolean addToO = m_Constraint.inO(down, up);
				result.addRank(down, up, rank, addToO);
			}
			
			for (int i=0; i<m_UnrestrictedRank.length; i++) {
				DoubleDecker<STATE> dd = m_UnrestrictedDoubleDecker.get(i);
				STATE down = dd.getDown();
				STATE up = dd.getUp();
				int rank = m_UnrestrictedRank[i];
				boolean addToO = m_Constraint.inO(down, up) && (rank % 2 == 0);
				result.addRank(down, up, rank, addToO);
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
	 * If a DoubleDecker has an even rank it must the the highest possible even
	 * rank.
	 * Warning: I think a restriction to LevelRanking that satisfy also the
	 * latter property leads to a sound complementation, but it is not mentioned
	 * in any paper and I do not have a proof for that. 
	 */
	public class MatthiasTightLevelRankingStateGenerator extends
											TightLevelRankingStateGenerator {

		public MatthiasTightLevelRankingStateGenerator(
						LevelRankingConstraint constraints) {
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










}
