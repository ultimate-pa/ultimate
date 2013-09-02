package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;


/**
 * Single static assignment form of a nested trace with a precondition and a
 * postcondition.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class NestedSsa {
	
	/**
	 * Trace for which this is the single static assignment form.
	 */
	private final NestedWord<CodeBlock> m_NestedTrace;
	
	/**
	 * SSA form of Precondition.
	 * Original precondition where all variables get index -1.  
	 */
	private Term m_Precondition;
	
	/**
	 * SSA form of Postcondition. 
	 * Original postcondition where all variables get as index the last position
	 * of the trace where this variable has been modified (with respect to 
	 * calling context).  
	 */
	private Term m_Postcondition;
	
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
	 * Maps a pending return position to a formula which represents the state of
	 * the procedure to which is returned before the return.
	 */
	private final SortedMap<Integer,Term> m_PendingContexts;
	
	
	/**
	 * Maps indexed variables (represented by terms) to the BoogieVar which
	 * represented the non-indexed version of the term.
	 */
	private final Map<Term, BoogieVar> m_Constants2BoogieVar;


	/**
	 * @param nestedTrace
	 * @param terms
	 * @param localVarAssignmentAtCall
	 * @param globalOldVarAssignmentAtCall
	 * @param pendingContexts
	 * @param constants2BoogieVar
	 */
	public NestedSsa(NestedWord<CodeBlock> nestedTrace, Term[] terms,
			Map<Integer, Term> localVarAssignmentAtCall,
			Map<Integer, Term> globalOldVarAssignmentAtCall,
			SortedMap<Integer, Term> pendingContexts, 
			Map<Term, BoogieVar> constants2BoogieVar) {
		m_NestedTrace = nestedTrace;
		m_Terms = terms;
		m_LocalVarAssignmentAtCall = localVarAssignmentAtCall;
		m_GlobalOldVarAssignmentAtCall = globalOldVarAssignmentAtCall;
		m_PendingContexts = pendingContexts;
		m_Constants2BoogieVar = constants2BoogieVar;
	}

	public NestedWord<CodeBlock> getTrace() {
		return m_NestedTrace;
	}


	public Term[] getFormulas() {
		return m_Terms;
	}


	public Map<Integer, Term> getLocalVarAssignmentAtCall() {
		return m_LocalVarAssignmentAtCall;
	}


	public Map<Integer, Term> getGlobalOldVarAssignmentAtCall() {
		return m_GlobalOldVarAssignmentAtCall;
	}
	
	public SortedMap<Integer, Term> getPendingContexts() {
		return m_PendingContexts;
	}


	public Map<Term, BoogieVar> getConstants2BoogieVar() {
		return m_Constants2BoogieVar;
	}


	public Term getPrecondition() {
		return m_Precondition;
	}

	@Deprecated
	public void setPrecondition(Term precondition) {
		m_Precondition = precondition;
	}


	public Term getPostcondition() {
		return m_Postcondition;
	}


	@Deprecated
	public void setPostcondition(Term postcondition) {
		m_Postcondition = postcondition;
	}
	
	

}
