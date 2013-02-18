package local.stalin.automata.nwalibrary;

import java.util.ArrayList;

public class NestedRun<Symbol,Content> {
	
	private NestedWord<Symbol> m_NestedWord;
	private ArrayList<IState<Symbol,Content>> m_StateSequence;
	
	public NestedRun(NestedWord<Symbol> nw,
					ArrayList<IState<Symbol,Content>> stateSequence) {
		if (nw.length()+1 == stateSequence.size()) {
			this.m_NestedWord = nw;
			this.m_StateSequence = stateSequence;
		}
		else {
			throw new IllegalArgumentException("In a run the length of the" +
					" sequence of states is length of the word plus 1.");
		}
	}
	
	/**
	 * Constructor for a run of length 1. 
	 */

	public NestedRun(IState<Symbol,Content> state) {
		m_StateSequence = new ArrayList<IState<Symbol,Content>>(1);
		m_StateSequence.add(state);
		@SuppressWarnings("unchecked")
		Symbol[] word =  (Symbol[])new Object[] { };
		int[] nestingRelation = {};
		m_NestedWord = new NestedWord<Symbol>(word, nestingRelation);
	}

	/**
	 * Constructor for a run of length 2. 
	 */
	public NestedRun(IState<Symbol,Content> q0,
			 		  Symbol symbol,
			 		  int position,
			 		  IState<Symbol,Content> q1) {
		if (position != NestedWord.INTERNAL_POSITION
			&& position != NestedWord.MINUS_INFINITY
			&& position != NestedWord.PLUS_INFINITY) {
			throw new IllegalArgumentException();
		}
		@SuppressWarnings("unchecked")
		Symbol[] word = (Symbol[])new Object[] {symbol};
		int[] nestingRelation = { position };
		m_NestedWord = new NestedWord<Symbol>(word,nestingRelation);
		m_StateSequence = new ArrayList<IState<Symbol,Content>>(2);
		m_StateSequence.add(q0);
		m_StateSequence.add(q1);
	}
	
		
	
	public NestedWord<Symbol> getNestedWord() {
		return this.m_NestedWord;
	}
	
	
	public ArrayList<IState<Symbol,Content>> getStateSequence() {
		return this.m_StateSequence;
	}
	
	
	/**
	 * Length of this runs state sequence.
	 */	
	public int getLength() {
		return this.m_StateSequence.size();
	}
		
	/**
	 * @param i
	 * @return
	 * @see local.stalin.automata.nwalibrary.NestedWord#isCallPosition(int)
	 */
	public boolean isCallPosition(int i) {
		return m_NestedWord.isCallPosition(i);
	}

	

	/**
	 * @param i
	 * @return
	 * @see local.stalin.automata.nwalibrary.NestedWord#isInternalPosition(int)
	 */
	public boolean isInternalPosition(int i) {
		return m_NestedWord.isInternalPosition(i);
	}

	/**
	 * @param i
	 * @return
	 * @see local.stalin.automata.nwalibrary.NestedWord#isReturnPosition(int)
	 */
	public boolean isReturnPosition(int i) {
		return m_NestedWord.isReturnPosition(i);
	}

	/**
	 * @param i
	 * @return
	 * @see local.stalin.automata.nwalibrary.NestedWord#isPendingCall(int)
	 */
	public boolean isPendingCall(int i) {
		return m_NestedWord.isPendingCall(i);
	}

	public NestedRun<Symbol,Content> concatenate(NestedRun<Symbol,Content> run) {
		IState<Symbol,Content> lastStateOfThis = m_StateSequence.get(m_StateSequence.size()-1);
		IState<Symbol,Content> firstStateOfRun = run.m_StateSequence.get(0);
		
		if (lastStateOfThis == firstStateOfRun) {
	
		NestedWord<Symbol> concatNestedWord =
			m_NestedWord.concatenate(run.getNestedWord());
			ArrayList<IState<Symbol,Content>> concatStateSeq =
					new ArrayList<IState<Symbol,Content>>(m_StateSequence);
			for (int i=1; i<run.getStateSequence().size(); i++) {
				concatStateSeq.add(run.getStateSequence().get(i));
			}
			return new NestedRun<Symbol, Content>(concatNestedWord,concatStateSeq);
		}
		else {
			throw new IllegalArgumentException("Can only concatenate two runs" +
					" where the last element of the first runs statement" +
					" sequence is the same state as the last element of the" +
					" second runs statement sequence."); 
		}
	}
		

	
	public IState<Symbol,Content> getStateAtPosition(int i) {
		return m_StateSequence.get(i);
	}
	
	public Symbol getSymbol(int i) {
		return m_NestedWord.getSymbolAt(i);
	}
	

	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i<m_NestedWord.length(); i++) {
			sb.append(getStateAtPosition(i) + " ");
			if (m_NestedWord.isInternalPosition(i)) {
				sb.append(m_NestedWord.getSymbolAt(i)+" ");
			}
			else if (m_NestedWord.isCallPosition(i)) {
				sb.append(m_NestedWord.getSymbolAt(i)+"< ");
			}
			else if (m_NestedWord.isReturnPosition(i)) {
				sb.append("> " + m_NestedWord.getSymbolAt(i));
			}
		}
		sb.append(getStateAtPosition(m_StateSequence.size()-1) + " ");
		return sb.toString();
	}
	
}
