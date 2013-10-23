package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * NestedFormulas where we can set formulas after construction of the object.
 * @author Matthias Heizmann
 *
 * @param <TF> formula for transitions
 * @param <SF> formula for states
 */
public class ModifiableNestedFormulas<TF, SF> extends
		NestedFormulas<TF, SF> {
	
	
	/**
	 * If index i is an internal position or a return transition in the
	 * nested trace Term[i] represents the i-th statement.
	 * If index i is a call position Term[i] represents the assignment 
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final TF[] m_Terms;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code x_1,...,x_n := t_1,...,t_n} where x_1,...,x_n are the parameters
	 * of the callee and t_1,...,t_n are the arguments of the caller.
	 */
	private final Map<Integer,TF> m_LocalVarAssignmentAtCall =
			new HashMap<Integer,TF>();
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer,TF> m_GlobalOldVarAssignmentAtCall =
			new HashMap<Integer,TF>();
	

	public ModifiableNestedFormulas(
			NestedWord<CodeBlock> nestedWord, SortedMap<Integer, SF> pendingContexts) {
		super(nestedWord, pendingContexts);
		m_Terms = (TF[]) new Object[nestedWord.length()];
	}

	@Override
	protected TF getFormulaFromValidNonCallPos(int i) {
		return m_Terms[i];
	}

	@Override
	protected TF getLocalVarAssignmentFromValidPos(int i) {
		return m_LocalVarAssignmentAtCall.get(i);
	}

	@Override
	protected TF getGlobalVarAssignmentFromValidPos(int i) {
		return m_Terms[i];
	}

	@Override
	protected TF getOldVarAssignmentFromValidPos(int i) {
		return m_GlobalOldVarAssignmentAtCall.get(i);
	}
	
	void setFormulaAtNonCallPos(int i, TF tf) {
		assert !super.getTrace().isCallPosition(i);
		assert m_Terms[i] == null : "already set";
		m_Terms[i] = tf;
	}
	
	void setLocalVarAssignmentAtPos(int i, TF tf) {
		assert super.getTrace().isCallPosition(i) || super.getTrace().isPendingReturn(i);
		assert m_LocalVarAssignmentAtCall.get(i) == null : "already set";
		m_LocalVarAssignmentAtCall.put(i, tf);
	}
	
	void setOldVarAssignmentAtPos(int i, TF tf) {
		assert super.getTrace().isCallPosition(i) || super.getTrace().isPendingReturn(i);
		assert m_GlobalOldVarAssignmentAtCall.get(i) == null : "already set";
		m_GlobalOldVarAssignmentAtCall.put(i, tf);
	}
	
	void setGlobalVarAssignmentAtPos(int i, TF tf) {
		assert super.getTrace().isCallPosition(i) || super.getTrace().isPendingReturn(i);
		assert m_Terms[i] == null : "already set";
		m_Terms[i] = tf;
	}

	
	

}
