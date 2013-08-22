package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;



public class RelevantTransFormulas {
	/**
	 * Trace for which the relevant transformula are computed.
	 */
	private final NestedWord<CodeBlock> m_NestedTrace;
	
	/**
	 * If index i is an internal position or a return transition in the
	 * nested trace Term[i] represents the i-th statement.
	 * If index i is a call position Term[i] represents the assignment 
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final TransFormula[] m_TransFormulas;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer,TransFormula> m_GlobalOldVarAssignmentTransFormulaAtCall;
	
	
	private final SmtManager m_SmtManager;
	
	public RelevantTransFormulas(NestedWord<CodeBlock> nestedTrace, 
			Set<CodeBlock> unsat_core,
			ModifiableGlobalVariableManager modGlobalVarManager,
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			SmtManager smtManager) {
		m_NestedTrace = nestedTrace;
		m_TransFormulas = new TransFormula[nestedTrace.length()];
		m_GlobalOldVarAssignmentTransFormulaAtCall = new HashMap<Integer, TransFormula>();
		m_SmtManager = smtManager;
		generateRelevantTransFormulas(unsat_core, localVarAssignmentsAtCallInUnsatCore, modGlobalVarManager);
	}
	
	public TransFormula getRelevantTransFormulaAtPosition(int i) {
		assert i >= 0 && i < m_TransFormulas.length : "TransFormula at position " + i + " is not available!";
		return m_TransFormulas[i];
	}
	
	public TransFormula getGlobalVarAssignmentAtCallPosition(int i) {
		assert m_GlobalOldVarAssignmentTransFormulaAtCall.containsKey(i) : "TransFormula for global variable assignment " +
				"at position " + i + " is not available!";
		return m_GlobalOldVarAssignmentTransFormulaAtCall.get(i);
	}
	
	private void generateRelevantTransFormulas(Set<CodeBlock> unsat_core, 
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			ModifiableGlobalVariableManager modGlobalVarManager) {
		for (int i = 0; i < m_NestedTrace.length(); i++) {
			if (unsat_core.contains(m_NestedTrace.getSymbol(i))) {
				if (m_NestedTrace.getSymbol(i) instanceof Call) {
					m_GlobalOldVarAssignmentTransFormulaAtCall.put(i,
							modGlobalVarManager.getGlobalVarsAssignment(((Call)m_NestedTrace.getSymbol(i)).getCallStatement().getMethodName()));
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						m_TransFormulas[i] = m_NestedTrace.getSymbol(i).getTransitionFormula();
					} else {
						m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(m_NestedTrace.getSymbol(i).getTransitionFormula());
					}
					
				} else {
					m_TransFormulas[i] = m_NestedTrace.getSymbol(i).getTransitionFormula();
				}
			} else {
				if (m_NestedTrace.getSymbol(i) instanceof Call) {
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						m_TransFormulas[i] = m_NestedTrace.getSymbol(i).getTransitionFormula();
					} else {
						m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(m_NestedTrace.getSymbol(i).getTransitionFormula());
					}
					m_GlobalOldVarAssignmentTransFormulaAtCall.put(i, buildTransFormulaForStmtNotInUnsatCore(
							modGlobalVarManager.getGlobalVarsAssignment(((Call)m_NestedTrace.getSymbol(i)).getCallStatement().getMethodName())));
				} else {
					m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(m_NestedTrace.getSymbol(i).getTransitionFormula());
				}
			}
		}
		
	}
	
	private TransFormula buildTransFormulaForStmtNotInUnsatCore(TransFormula tf) {
		Map<BoogieVar, TermVariable> outvars = new HashMap<BoogieVar, TermVariable>();
		for (BoogieVar bv : tf.getAssignedVars()) {
			if (tf.getOutVars().containsKey(bv)) {
				outvars.put(bv, tf.getOutVars().get(bv));
			}
		}
		
		return new TransFormula(m_SmtManager.newTruePredicate().getFormula(),
				new HashMap<BoogieVar, TermVariable>(),
				outvars,
				tf.getAuxVars(), 
				tf.getBranchEncoders(),
				tf.isInfeasible(),
				tf.getClosedFormula());
	}

}
