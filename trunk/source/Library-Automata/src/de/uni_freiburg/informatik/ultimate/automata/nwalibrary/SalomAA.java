package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;


public class SalomAA<LETTER, STATE> implements IAutomaton<LETTER, STATE> {
	
	/**
	 * The transition relation for each state and letter is described by a set of integers. 
	 * An Integer stands for a bitvector. A bitvector represents the conjunction of states 
	 * (negated or not). The set of bitvectors represents a DNF.
	 */
	private HashMap<STATE, HashMap<LETTER, DNFAsBitSetList>> m_TransitionFunction;
	
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
	DNFAsBitSetList m_acceptingFunction;
	
	/**
	 * Set of final states, represented as characteristic bitvector.
	 */
	BitSet m_finalStates;

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
		this.m_finalStates = new BitSet();
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
		m_finalStates.set(stateIndex);
	}


	/**
	 * Adds the disjunct q_stateIndex to the accepting function.
	 * @param stateIndex
	 */
	private void addInitialStateByIndex(int stateIndex) {
		DNFAsBitSetList stateRep = computeIntsFromSingleState(stateIndex);
		if (m_acceptingFunction == null) {
			m_acceptingFunction = stateRep;
		} else {
			m_acceptingFunction.insert(stateRep);
		}
	}
	
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
		
		HashMap<LETTER, DNFAsBitSetList> letterToSuccFormula = m_TransitionFunction.get(sourceState);
		if (letterToSuccFormula == null) {
			letterToSuccFormula = new HashMap<>();
			m_TransitionFunction.put(sourceState, letterToSuccFormula);
		}
		DNFAsBitSetList succFormula = m_TransitionFunction.get(sourceState).get(letter);
		if (succFormula == null) {
			m_TransitionFunction.get(sourceState).put(letter, computeConjunctionFromStateSet(succs));
		} else {
			m_TransitionFunction.get(sourceState).get(letter).insert(computeConjunctionFromStateSet(succs));
		}
	}

	private DNFAsBitSetList computeConjunctionFromStateSet(Set<STATE> succs) {
		BitSet alpha = new BitSet();
		BitSet beta = new BitSet();

		for (int i = 0; i < m_stateList.size(); i++) {
			if (succs.contains(m_stateList.get(i))) {
				alpha.set(i);
				beta.set(i);
			}
		}
		return new DNFAsBitSetList(alpha, beta, null);
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
		
		HashMap<LETTER, DNFAsBitSetList> letterToSuccFormula = m_TransitionFunction.get(sourceState);
		if (letterToSuccFormula == null) {
			letterToSuccFormula = new HashMap<>();
			m_TransitionFunction.put(sourceState, letterToSuccFormula);
		}
		DNFAsBitSetList succFormula = m_TransitionFunction.get(sourceState).get(letter);
		if (succFormula == null) {
			succFormula = 
			m_TransitionFunction.get(sourceState).put(letter, computeIntsFromSingleState(succ));
		} else {
			m_TransitionFunction.get(sourceState).get(letter).insert(computeIntsFromSingleState(succ));
		}
	}

	private DNFAsBitSetList computeIntsFromSingleState(STATE state) {
		Integer stateIndex = m_stateToIndex.get(state);
		if (stateIndex != null) {
			return computeIntsFromSingleState(stateIndex);
		}
		throw new UnsupportedOperationException("tried to compute an int of a bitvector for a state that is not in the state list.");
	}
	private DNFAsBitSetList computeIntsFromSingleState(int stateIndex) {
		BitSet alpha = new BitSet();
		alpha.set(stateIndex);
		BitSet beta = new BitSet();
		beta.set(stateIndex);
		return new DNFAsBitSetList(alpha, beta, null);
	}
	
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
//		sb.append("final states" + prettyPrintBitVector(m_finalStates) + "\n");
		sb.append("final states" + m_finalStates + "\n");

		StringBuilder sbTf = new StringBuilder();
		for (Entry<STATE, HashMap<LETTER, DNFAsBitSetList>> en1 : this.m_TransitionFunction.entrySet()) {
			for (Entry<LETTER, DNFAsBitSetList> en2 : en1.getValue().entrySet()) {
				STATE sourceState = en1.getKey();
				LETTER letter = en2.getKey();
				DNFAsBitSetList dnf = en2.getValue();	
				StringBuilder dnfSb = new StringBuilder();
				dnf.prettyPrintDNF(dnfSb, m_stateList);
				sbTf.append(sourceState + " |-> " + letter + " |-> " + dnfSb.toString() + "\n");
			}
		}
		sb.append("transition function: \n" + sbTf.toString());

		StringBuilder dnfSb = new StringBuilder();
		m_acceptingFunction.prettyPrintDNF(dnfSb, m_stateList);
		sb.append("accepting function : " + dnfSb.toString() + "\n");
		return sb.toString();
	}
	
	public Logger getLogger() {
		return m_logger;
	}
	
	

	public HashMap<STATE, HashMap<LETTER, DNFAsBitSetList>> getTransitionFunction() {
		return m_TransitionFunction;
	}

	public void setTransitionFunction(
			HashMap<STATE, HashMap<LETTER, DNFAsBitSetList>> m_TransitionFunction) {
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

	public DNFAsBitSetList getAcceptingFunction() {
		return m_acceptingFunction;
	}

	public void setAcceptingFunction(DNFAsBitSetList m_acceptingFunction) {
		this.m_acceptingFunction = m_acceptingFunction;
	}

	public BitSet getFinalStates() {
		return m_finalStates;
	}

	public void setFinalStates(BitSet m_finalStates) {
		this.m_finalStates = m_finalStates;
	}



	
	
	
}
