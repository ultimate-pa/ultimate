package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;


//TODO: 32 states werden nicht reichen, sobald ein trace auftritt, der einen RD-DAG der Größe >32 hat.. --> BitSets!
public class SalomAA<LETTER, STATE> implements IAutomaton<LETTER, STATE> {
	
	/**
	 * The transition relation for each state and letter is described by a set of integers. 
	 * An Integer stands for a bitvector. A bitvector represents the conjunction of states 
	 * (negated or not). The set of bitvectors represents a DNF.
	 */
	private HashMap<STATE, HashMap<LETTER, DNFAsInts>> m_TransitionFunction;
	
	/**
	 * List of all states of the automaton, note that the index of the state in this
	 * list is the one relevant for the bitvector encoding of state sets for the transition
	 * function.
	 */
	private ArrayList<STATE> m_stateList;

	/**
	 * Maps all states to their index in m_stateList. (Thus provides the reverse function
	 * of the one implicit in m_stateList.)
	 */
	private HashMap<STATE, Integer> m_stateToIndex;
	
	/**
	 * Generalisation of initial state (set), called h in the papers.
	 */
	DNFAsInts m_acceptingFunction;
	
	/**
	 * Set of final states, represented as characteristic bitvector.
	 */
	long m_finalStates;

	private Set<LETTER> m_Alphabet;
	protected final StateFactory<STATE> m_StateFactory;
	
	private Logger m_logger;

	
	public SalomAA(Logger logger, Set<LETTER> alphabet, StateFactory<STATE> stateFactory) {
		if (alphabet == null) {
			throw new IllegalArgumentException("The AA must have an alphabet");
		}
		if (stateFactory == null) {
			throw new IllegalArgumentException("The AA must have a stateFactory");
		}
		this.m_Alphabet = alphabet;
		this.m_StateFactory = stateFactory;
		this.m_stateToIndex = new HashMap<>();
		this.m_stateList = new ArrayList<>();
		this.m_finalStates = 0;
		this.m_TransitionFunction = new HashMap<>();
		this.m_logger = logger;
	}
	
	/**
	 * Create a SalomAA from a "normal" AA
	 * @param aa
	 */
	public SalomAA(AlternatingAutomaton<LETTER, STATE> aa) {
		m_StateFactory = aa.getStateFactory();
		m_Alphabet = aa.getAlphabet();
		for (STATE s : aa.getStates())
			this.addState(aa.getInitialStates().contains(s), 
					aa.getFinalStates().contains(s),
					s);
		for (Entry<STATE, Map<LETTER, Set<STATE>>> en1 : aa.getTransitionsMap().entrySet()) {
			for (Entry<LETTER, Set<STATE>> en2 : en1.getValue().entrySet()) {
				STATE sourceState = en1.getKey();
				LETTER letter = en2.getKey();
				Set<STATE> successors = en2.getValue();
				if (aa.getUniversalStates().contains(sourceState)) {
					this.addTransitionConjunction(sourceState, letter, successors);
				} else {
					for (STATE successor : successors) {
						this.addTransitionDisjunct(sourceState, letter, successor);
					}
				}
			}
			
		}
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return m_Alphabet;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}

	public void addState(boolean isInitial, boolean isFinal, STATE state) {
//		assert m_stateToIndex.containsValue(state) : "the same state should not be added twice";
		if (m_stateToIndex.containsKey(state)) {
			return;
		}
		m_stateList.add(state);
		assert m_stateList.size() < 32 : "our representation can deal with 32-state-rAFAs at the most --> perhaps we should fix this..";

		int stateIndex = m_stateList.size() - 1;
		m_stateToIndex.put(state, stateIndex);

		if (isInitial)
			addInitialStateByIndex(stateIndex);
		if (isFinal)
			addFinalState(stateIndex);
	}

	private void addFinalState(int stateIndex) {
		m_finalStates += twoToThe(stateIndex);
	}


	/**
	 * Adds the disjunct q_stateIndex to the accepting function.
	 * @param stateIndex
	 */
	private void addInitialStateByIndex(int stateIndex) {
		DNFAsInts stateRep = computeIntsFromSingleState(stateIndex);
		if (m_acceptingFunction == null) {
			m_acceptingFunction = stateRep;
		} else {
			m_acceptingFunction.insert(stateRep);
		}
	}
	
//	public boolean isFinal(STATE state) {
//		return isFinal(m_stateToIndex.get(state));
//	}
//
//	private boolean isFinal(int stateIndex) {
//		return (m_finalStates & twoToThe(stateIndex))/twoToThe(stateIndex) == 1;
//	}

//	public boolean isInitial(STATE state) {
//		return isFinal(m_stateToIndex.get(state));
//	}

//	private boolean isInitial(int stateIndex) {
//		return (m_initialStates & twoToThe(stateIndex))/twoToThe(stateIndex) == 1;
//	}

	/**
	 * Add a conjunction of positive boolean variables to the transition function of sourceState, letter
	 * according to the state set
	 * @param sourceState
	 * @param letter
	 * @param succs
	 */
	public void addTransitionConjunction(STATE sourceState, LETTER letter, Set<STATE> succs) {
		m_logger.debug("transition function update: " + sourceState + "->" + letter + "->" + succs);
		if (!m_stateToIndex.containsKey(sourceState))
			addState(false, false, sourceState);
		for (STATE succ : succs) {
			if (!m_stateToIndex.containsKey(succ))
				addState(false, false, sourceState);
		}
		
		HashMap<LETTER, DNFAsInts> letterToSuccFormula = m_TransitionFunction.get(sourceState);
		if (letterToSuccFormula == null) {
			letterToSuccFormula = new HashMap<>();
			m_TransitionFunction.put(sourceState, letterToSuccFormula);
		}
		DNFAsInts succFormula = m_TransitionFunction.get(sourceState).get(letter);
		if (succFormula == null) {
			m_TransitionFunction.get(sourceState).put(letter, computeConjunctionFromStateSet(succs));
		} else {
			m_TransitionFunction.get(sourceState).get(letter).insert(computeConjunctionFromStateSet(succs));
		}
	}

	private DNFAsInts computeConjunctionFromStateSet(Set<STATE> succs) {
		long alpha = 0;
		long beta = 0;

		for (int i = 0; i < m_stateList.size(); i++) {
			if (succs.contains(m_stateList.get(i))) {
				alpha += twoToThe(i);
				beta += twoToThe(i);
			}
		}
		return new DNFAsInts(alpha, beta, null);
	}

	/**
	 * 
	 * @param sourceState
	 * @param letter
	 * @param succs
	 */
	public void addTransitionDisjunct(STATE sourceState, LETTER letter, STATE succ) {
		m_logger.debug("transition function update: " + sourceState + "->" + letter + "->" + succ);
		if (!m_stateToIndex.containsKey(sourceState))
			addState(false, false, sourceState);
		if (!m_stateToIndex.containsKey(succ))
			addState(false, false, sourceState);
		
		HashMap<LETTER, DNFAsInts> letterToSuccFormula = m_TransitionFunction.get(sourceState);
		if (letterToSuccFormula == null) {
			letterToSuccFormula = new HashMap<>();
			m_TransitionFunction.put(sourceState, letterToSuccFormula);
		}
		DNFAsInts succFormula = m_TransitionFunction.get(sourceState).get(letter);
		if (succFormula == null) {
			succFormula = 
			m_TransitionFunction.get(sourceState).put(letter, computeIntsFromSingleState(succ));
		} else {
			m_TransitionFunction.get(sourceState).get(letter).insert(computeIntsFromSingleState(succ));
		}
	}

	private DNFAsInts computeIntsFromSingleState(STATE state) {
		Integer stateIndex = m_stateToIndex.get(state);
		if (stateIndex != null) {
			return computeIntsFromSingleState(stateIndex);
		}
		throw new UnsupportedOperationException("tried to compute an int of a bitvector for a state that is not in the state list.");
	}
	private DNFAsInts computeIntsFromSingleState(int stateIndex) {
		long tttSi = twoToThe(stateIndex);
		return new DNFAsInts(tttSi, tttSi, null);
	}
	
	private String prettyPrintBitVector(long bvAsInt) {
		Boolean[] bv = new Boolean[m_stateList.size()];
		for (int i = 0; i < m_stateList.size(); i++) {
			bv[i] = (bvAsInt & twoToThe(i))/twoToThe(i) == 1;
		}
		return Arrays.toString(bv);
	}

	private long twoToThe(long x) {
		assert x < 31 : "we need longs..";
		return 1 << x; //with leftshift it is fastest, right?
//		int result = 1;
//		for (int i = 0; i < x; i++) {
//			result *= 2; 
//		}
//		return result;
	}
	
//	/**
//	 * Returns an int that corresponds to the bitvector representation of
//	 * the input state set (according to the indices in m_stateList).
//	 * @param succs
//	 * @return
//	 */
//	private Integer computeIntsFromStateSet(Set<STATE> succs) {
//		//what is better? 
//		// going over all the states in m_stateList?
//		// or using the hashmap to only use the needed indices?
//		int result = 0;
//		//for now: going over all the states
//		for (int i = 0; i < m_stateList.size(); i++) {
//			if (succs.contains(m_stateList.get(i))) {
//				result += twoToThe(i);
//			}
//		}
//		return result;
//	}
	
	public List<STATE> getStates() {
		return m_stateList;
	}

	@Override
	public int size() {
		return m_stateList.size();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("alphabet = " + this.getAlphabet() + "\n");
		sb.append("state set = " + this.getStates() + "\n");
		sb.append("final states" + prettyPrintBitVector(m_finalStates) + "\n");

		StringBuilder sbTf = new StringBuilder();
		for (Entry<STATE, HashMap<LETTER, DNFAsInts>> en1 : this.m_TransitionFunction.entrySet()) {
			for (Entry<LETTER, DNFAsInts> en2 : en1.getValue().entrySet()) {
				STATE sourceState = en1.getKey();
				LETTER letter = en2.getKey();
				DNFAsInts dnf = en2.getValue();	
				StringBuilder dnfSb = new StringBuilder();
				dnf.prettyPrintDNF(dnfSb);
				sbTf.append(sourceState + " |-> " + letter + " |-> " + dnfSb.toString() + "\n");
			}
		}
		sb.append("transition function: \n" + sbTf.toString());

		StringBuilder dnfSb = new StringBuilder();
		m_acceptingFunction.prettyPrintDNF(dnfSb);
		sb.append("accepting function : " + dnfSb.toString() + "\n");
		return sb.toString();
	}
	
	public Logger getLogger() {
		return m_logger;
	}
	
	

	public HashMap<STATE, HashMap<LETTER, DNFAsInts>> getM_TransitionFunction() {
		return m_TransitionFunction;
	}

	public void setTransitionFunction(
			HashMap<STATE, HashMap<LETTER, DNFAsInts>> m_TransitionFunction) {
		this.m_TransitionFunction = m_TransitionFunction;
	}

	public ArrayList<STATE> getStateList() {
		return m_stateList;
	}

	public void setStateList(ArrayList<STATE> m_stateList) {
		this.m_stateList = m_stateList;
	}

	public HashMap<STATE, Integer> getStateToIndex() {
		return m_stateToIndex;
	}

	public void setStateToIndex(HashMap<STATE, Integer> m_stateToIndex) {
		this.m_stateToIndex = m_stateToIndex;
	}

	public DNFAsInts getAcceptingFunction() {
		return m_acceptingFunction;
	}

	public void setAcceptingFunction(DNFAsInts m_acceptingFunction) {
		this.m_acceptingFunction = m_acceptingFunction;
	}

	public long getFinalStates() {
		return m_finalStates;
	}

	public void setFinalStates(long m_finalStates) {
		this.m_finalStates = m_finalStates;
	}



	/**
	 * Salomaa style representation of a DNF as a list of conjunctions.
	 * Each conjunction is stored as two ints.
	 * alpha says whiche state variables appear in the conjunction.
	 * beta says whether the appearing ones appera positive or negative.
	 */
	class DNFAsInts {
		long alpha;
		long beta;
		DNFAsInts next;

		public DNFAsInts(long alpha, long beta, DNFAsInts next) {
			super();
			this.alpha = alpha;
			this.beta = beta;
			this.next = next;
		}
		
		void insert(DNFAsInts dai) {
			if (this.next == null) {
				this.next = dai;
			} else {
				this.next.insert(dai);
			}
		}
		
		public void prettyPrintDNF(StringBuilder sb) {
			if (sb.toString().equals(""))
				sb.append(" \\/ (");
			
			String comma = "";
			for (int i = 0; i < m_stateList.size(); i++) {
				if (alpha != 0 && i == 0)
					sb.append(" /\\ {");
				boolean isStateVariablePresent = (alpha & twoToThe(i))/twoToThe(i) == 1;
				boolean isStateVariablePositive = (beta & twoToThe(i))/twoToThe(i) == 1;
				if (isStateVariablePresent) {
					if (!isStateVariablePositive) {
						sb.append(" not");
					}
//					sb.append(comma + i); // or put the state here?
					sb.append(comma + m_stateList.get(i)); // or put the state here?
					comma = ", ";
				}
				if (alpha != 0 && i == m_stateList.size() - 1)
					sb.append("}, ");
			}
			if (next != null)
				next.prettyPrintDNF(sb);
			else 
				sb.append(")\n");
		}
	}
	
	
}
