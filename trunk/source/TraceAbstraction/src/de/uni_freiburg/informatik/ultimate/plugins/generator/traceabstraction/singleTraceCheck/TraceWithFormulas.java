package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Class that represents a sequence of formulas (of type F) along a trace (given
 * by a NestedWord<CodeBlock>). At each non-call position there is one formula.
 * At each call positions there are three formulas
 * <ul>
 * <li> one that represents an assignment of certain local variables namely the
 * (input) parameters of the called procedure,
 * <li> one that represents an assignment of all global variables that may be
 * modified by the called procedure, and
 * <li> one that represents an assignment of all oldvars of global variables 
 * that may be modified by the called procedure.
 * The class uses assertions to check that indices for all public getters of 
 * this class are valid. Subclasses have to override the methods with the 
 * <i>FromValidPos</i> suffix and may assume that validity of the index was 
 * checked (in case assertions are enabled)
 * 
 * @author Matthias Heizmann
 *
 * @param <F> Type of the formulas along the trace.
 */
public abstract class TraceWithFormulas<F> {
	
	private final NestedWord<CodeBlock> m_NestedWord;
	
	public NestedWord<CodeBlock> getTrace() {
		return m_NestedWord;
	}
	
	public TraceWithFormulas(NestedWord<CodeBlock> nestedWord) {
		m_NestedWord = nestedWord;
	}
	
	public abstract Set<Integer> callPositions();
	
	public final F getFormulaFromNonCallPos(int i) {
		assert i>=0 && i<m_NestedWord.length() : "out of range";
		assert !m_NestedWord.isCallPosition(i) : "call position";
		return getFormulaFromValidNonCallPos(i);
	}
	
	protected abstract F getFormulaFromValidNonCallPos(int i);
	
	
	
	public F getLocalVarAssignment(int i) {
		assert i>=0 && i<m_NestedWord.length() : "out of range";
		assert callPositions().contains(i) : "no call position";
		assert m_NestedWord.isCallPosition(i) : "no call position";
		return getLocalVarAssignmentFromValidPos(i);
	}
	
	protected abstract F getLocalVarAssignmentFromValidPos(int i);
	
	public F getGlobalVarAssignment(int i) {
		assert i>=0 && i<m_NestedWord.length() : "out of range";
		assert callPositions().contains(i) : "no call position";
		assert m_NestedWord.isCallPosition(i) : "no call position";
		return getLocalVarAssignmentFromValidPos(i);
	}
	
	protected abstract F getGlobalVarAssignmentFromValidPos(int i);
	
	public F getOldVarAssignment(int i) {
		assert i>=0 && i<m_NestedWord.length() : "out of range";
		assert callPositions().contains(i) : "no call position";
		assert m_NestedWord.isCallPosition(i) : "no call position";
		return getLocalVarAssignmentFromValidPos(i);
	}
	
	protected abstract F getOldVarAssignmentFromValidPos(int i);


}
