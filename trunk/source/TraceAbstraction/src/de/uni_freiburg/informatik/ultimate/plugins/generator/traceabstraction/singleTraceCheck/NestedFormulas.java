package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class NestedFormulas<F> {
	
	private final NestedWord<CodeBlock> m_NestedWord;
	
	private final List<F> m_Formulas;
	private final Map<Integer,F> m_LocalVarAssignment;
	private final Map<Integer,F> m_GlobalVarAssignment;
	private final Map<Integer,F> m_OldVarAssignment;
	
	public NestedFormulas(NestedWord<CodeBlock> nestedWord, List<F> formulas,
			Map<Integer, F> localVarAssignment,
			Map<Integer, F> globalVarAssignment,
			Map<Integer, F> oldVarAssignment) {
		super();
		m_NestedWord = nestedWord;
		m_Formulas = formulas;
		m_LocalVarAssignment = localVarAssignment;
		m_GlobalVarAssignment = globalVarAssignment;
		m_OldVarAssignment = oldVarAssignment;
	}
	
	public F getFormula(int i) {
		assert i>=0 && i<m_NestedWord.length() : "out of range";
		assert !m_NestedWord.isCallPosition(i) : "call position";
		return m_Formulas.get(i);
	}
	
	public Set<Integer> callPositions() {
		return m_LocalVarAssignment.keySet();
	}
	
	public F getLocalVarAssignment(int i) {
		assert callPositions().contains(i);
		assert getFormula(i)  == null;
		return m_LocalVarAssignment.get(i);
	}
	
	public F getGlobalVarAssignment(int i) {
		assert callPositions().contains(i);
		assert getFormula(i)  == null;
		return m_GlobalVarAssignment.get(i);
	}
	
	public F getOldVarAssignment(int i) {
		assert callPositions().contains(i);
		assert getFormula(i)  == null;
		return m_OldVarAssignment.get(i);
	}


}
