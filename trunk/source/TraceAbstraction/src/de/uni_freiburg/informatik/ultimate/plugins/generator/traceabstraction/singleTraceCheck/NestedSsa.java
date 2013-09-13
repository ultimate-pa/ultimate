package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;


/**
 * Single static assignment form of a nested trace with a precondition and a
 * postcondition.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class NestedSsa extends TraceWithFormulas<Term, Term> {
	
	/**
	 * If index i is an internal position or a return transition in the
	 * nested trace Term[i] represents the i-th statement.
	 * If index i is a call position Term[i] represents the assignment 
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Term[] m_Terms;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code x_1,...,x_n := t_1,...,t_n} where x_1,...,x_n are the parameters
	 * of the callee and t_1,...,t_n are the arguments of the caller.
	 */
	private final Map<Integer,Term> m_LocalVarAssignmentAtCall;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer,Term> m_GlobalOldVarAssignmentAtCall;
	
	/**
	 * Maps indexed variables (represented by terms) to the BoogieVar which
	 * represented the non-indexed version of the term.
	 */
	private final Map<Term, BoogieVar> m_Constants2BoogieVar;
	
	
	/**
	 * TransFormulas for which this SSA was computed.
	 */
	private final TraceWithFormulas<TransFormula, IPredicate> m_TransFormulas;


	/**
	 * @param nestedTrace
	 * @param terms
	 * @param localVarAssignmentAtCall
	 * @param globalOldVarAssignmentAtCall
	 * @param pendingContexts
	 * @param constants2BoogieVar
	 */
	public NestedSsa(TraceWithFormulas<TransFormula, IPredicate> traceWF, Term precondition, 
			Term postcondition, Term[] terms,
			Map<Integer, Term> localVarAssignmentAtCall,
			Map<Integer, Term> globalOldVarAssignmentAtCall,
			SortedMap<Integer, Term> pendingContexts, 
			Map<Term, BoogieVar> constants2BoogieVar) {
		super(traceWF.getTrace(), precondition, postcondition, pendingContexts);
		m_TransFormulas = traceWF;
		m_Terms = terms;
		m_LocalVarAssignmentAtCall = localVarAssignmentAtCall;
		m_GlobalOldVarAssignmentAtCall = globalOldVarAssignmentAtCall;
		m_Constants2BoogieVar = constants2BoogieVar;
	}

	public Map<Term, BoogieVar> getConstants2BoogieVar() {
		return m_Constants2BoogieVar;
	}

	@Override
	public Set<Integer> callPositions() {
		System.out.println("necessary?");
		return super.getTrace().computeCallPositions();
	}

	@Override
	protected Term getFormulaFromValidNonCallPos(int i) {
		return m_Terms[i];
	}

	@Override
	protected Term getLocalVarAssignmentFromValidPos(int i) {
		return m_LocalVarAssignmentAtCall.get(i);
	}

	@Override
	protected Term getGlobalVarAssignmentFromValidPos(int i) {
		return m_Terms[i];
	}

	@Override
	protected Term getOldVarAssignmentFromValidPos(int i) {
		return m_GlobalOldVarAssignmentAtCall.get(i);
	}

	public TraceWithFormulas<TransFormula, IPredicate> getTransFormulas() {
		return m_TransFormulas;
	}
	
	



}
