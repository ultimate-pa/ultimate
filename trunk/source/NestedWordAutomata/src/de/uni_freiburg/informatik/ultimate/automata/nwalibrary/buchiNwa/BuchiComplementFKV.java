package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DoubleDeckerBuilder;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKV<LETTER,STATE> extends DoubleDeckerBuilder<LETTER,STATE> 
									 implements IOperation {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is suffient, see paper of Seth Forgaty.
	 */
	int m_UserDefinedMaxRank = Integer.MAX_VALUE;
	
	private INestedWordAutomaton<LETTER,STATE> m_Operand;
	
	StateFactory<STATE> m_ContentFactory;
	
	/**
	 * Maps DeterminizedState to its representative in the resulting automaton.
	 */
	private Map<DeterminizedState<LETTER,STATE>,STATE> m_det2res =
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
	private Map<LevelRankingState,STATE> m_lrk2res =
		new HashMap<LevelRankingState, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the LevelRankingState for which it
	 * was created.
	 */
	private final Map<STATE,LevelRankingState> m_res2lrk =
		new HashMap<STATE, LevelRankingState>();
	
	private final PowersetDeterminizer<LETTER,STATE> m_PowersetDeterminizer;
	
	/**
	 * Highest rank that occured during the construction. Used only for
	 *  statistics.
	 */
	int m_HighestRank = -1;	
	
	
	
	@Override
	public String operationName() {
		return "buchiComplementFKV";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
			m_TraversedNwa.sizeInformation() + 
			"the highest rank that occured is " + m_HighestRank;
	}




	
	
	
	public BuchiComplementFKV(INestedWordAutomaton<LETTER,STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
//		((NestedWordAutomaton<LETTER,STATE>) m_Operand).buchiClosure();

		m_ContentFactory = m_Operand.getStateFactory();
		m_PowersetDeterminizer = new PowersetDeterminizer<LETTER,STATE>(m_Operand);
		super.m_TraversedNwa = new NestedWordAutomaton<LETTER,STATE>(
				m_Operand.getInternalAlphabet(),
				m_Operand.getCallAlphabet(),
				m_Operand.getReturnAlphabet(),
				m_Operand.getStateFactory());
//		m_RemoveDeadEnds = true;
		m_RemoveNonLiveStates = false;

		traverseDoubleDeckerGraph();
		s_Logger.info(exitMessage());
		assert (ResultChecker.buchiComplement(m_Operand, m_TraversedNwa));
	}
	

	@Override
	public INestedWordAutomaton<LETTER,STATE> getResult()
			throws OperationCanceledException {
		assert ResultChecker.buchiComplement(m_Operand, m_TraversedNwa);
		return m_TraversedNwa;
	}
	
	
	@Override
	protected Collection<STATE> getInitialStates() {
		ArrayList<STATE> resInitials = 
			new ArrayList<STATE>(m_Operand.getInitialStates().size());
		DeterminizedState<LETTER,STATE> detState = m_PowersetDeterminizer.initialState();
		STATE resState = getOrAdd(detState, true);
		resInitials.add(resState);

		return resInitials;
	}
	

	@Override
	protected Collection<STATE> buildInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> resSuccs = new ArrayList<STATE>();
		STATE resUp = doubleDecker.getUp();
		DeterminizedState<LETTER,STATE> detUp = m_res2det.get(resUp);
		if (detUp != null)
		for (LETTER symbol : m_Operand.getInternalAlphabet()) {
			{
				DeterminizedState<LETTER,STATE> detSucc = 
					m_PowersetDeterminizer.internalSuccessor(detUp, symbol);
				if (!detSucc.isEmpty()) {
					STATE resSucc = getOrAdd(detSucc, false);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(resUp, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingConstraint constraints = new LevelRankingConstraint();
			constraints.internalSuccessorConstraints(detUp, symbol);
			TightLevelRankingStateGenerator gen = 
				new MatthiasTightLevelRankingStateGenerator(constraints);
			Collection<LevelRankingState> result = gen.computeResult();
			for (LevelRankingState complSucc : result) {
				STATE resSucc = getOrAdd(complSucc);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(resUp, symbol, resSucc);
				resSuccs.add(resSucc);
			}
		}
		LevelRankingState complUp = m_res2lrk.get(resUp);
		if (complUp != null)
		for (LETTER symbol : m_Operand.getInternalAlphabet()) {
			LevelRankingConstraint constraints = new LevelRankingConstraint();
			constraints.internalSuccessorConstraints(complUp, symbol);
			TightLevelRankingStateGenerator gen = 
				new MatthiasTightLevelRankingStateGenerator(constraints);
			Collection<LevelRankingState> result = gen.computeResult();
			for (LevelRankingState complSucc : result) {
				STATE resSucc = getOrAdd(complSucc);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(resUp, symbol, resSucc);
				resSuccs.add(resSucc);
			}
		}
		return resSuccs;
	}
	
	
	@Override
	protected Collection<STATE> buildCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> resSuccs = new ArrayList<STATE>();
		return resSuccs;
	}
	
	@Override
	protected Collection<STATE> buildReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> resSuccs = new ArrayList<STATE>();
		return resSuccs;
	}
	

	/**
	 * Return state of result automaton that represents lrkState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(LevelRankingState lrkState) {
		STATE resSucc = m_lrk2res.get(lrkState);
		if (resSucc == null) {
			resSucc = lrkState.getContent();
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(false, lrkState.isOempty(), resSucc);
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
	STATE getOrAdd(DeterminizedState<LETTER,STATE> detState, boolean isInitial) {
		STATE resSucc = m_det2res.get(detState);
		if (resSucc == null) {
			resSucc = detState.getContent(m_ContentFactory);
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(isInitial, false, resSucc);
			m_det2res.put(detState, resSucc);
			m_res2det.put(resSucc, detState);
		}
		return resSucc;
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
	public class LevelRankingState {
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
			return m_ContentFactory.complementBuchi((LevelRankingState) this);
		}
		
		@Override
		public String toString() {
			return String.valueOf(getContent());
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
		private BuchiComplementFKV<LETTER,STATE> getOuterType() {
			return BuchiComplementFKV.this;
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
	class LevelRankingConstraint extends LevelRankingState {
		
		void internalSuccessorConstraints(DeterminizedState<LETTER,STATE> state, LETTER symbol) {
			boolean oCandidate = false;
			Integer upRank = Integer.MAX_VALUE;
			for (STATE down : state.getDownStates()) {
				for (STATE up : state.getUpStates(down)) {
					for (STATE succ : m_Operand.succInternal(up,symbol)) {
						addConstaint(down, succ, upRank, oCandidate);
					}
				}
			}
		}
		
		void internalSuccessorConstraints(LevelRankingState state, LETTER symbol) {
			for (STATE down : state.getDownStates()) {
				for (STATE up : state.getUpStates(down)) {
					boolean oCandidate = state.isOempty() || state.inO(down,up);
					Integer upRank = state.getRank(down, up);
					for (STATE succ : m_Operand.succInternal(up, symbol)) {
						addConstaint(down, succ, upRank, oCandidate);
					}
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
	private class TightLevelRankingStateGenerator {

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
		
		TightLevelRankingStateGenerator(LevelRankingConstraint constraint) {
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
	private class MatthiasTightLevelRankingStateGenerator extends
											TightLevelRankingStateGenerator {

		MatthiasTightLevelRankingStateGenerator(
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
