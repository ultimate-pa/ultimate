package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Class for computing the relevant transformulas of a trace with unsatisfiable core.
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class RelevantTransFormulas extends TraceWithFormulas<TransFormula, IPredicate> {
	
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
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer,TransFormula> m_GlobalAssignmentTransFormulaAtCall;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer, TransFormula> m_OldVarsAssignmentTransFormulasAtCall;
	
	
	private final SmtManager m_SmtManager;
	
	public RelevantTransFormulas(NestedWord<CodeBlock> nestedTrace,
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			Set<CodeBlock> unsat_core,
			ModifiableGlobalVariableManager modGlobalVarManager,
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			SmtManager smtManager) {
		super(nestedTrace, precondition, postcondition, pendingContexts);
		m_TransFormulas = new TransFormula[nestedTrace.length()];
		m_GlobalAssignmentTransFormulaAtCall = new HashMap<Integer, TransFormula>();
		m_OldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, TransFormula>();
		m_SmtManager = smtManager;
		generateRelevantTransFormulas(unsat_core, localVarAssignmentsAtCallInUnsatCore, modGlobalVarManager);
	}
	
	private void generateRelevantTransFormulas(Set<CodeBlock> unsat_core, 
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			ModifiableGlobalVariableManager modGlobalVarManager) {
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (unsat_core.contains(super.getTrace().getSymbol(i))) {
				if (super.getTrace().getSymbol(i) instanceof Call) {
					m_GlobalAssignmentTransFormulaAtCall.put(i,
							modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()));
					m_OldVarsAssignmentTransFormulasAtCall.put(i, 
							modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()));
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						m_TransFormulas[i] = super.getTrace().getSymbol(i).getTransitionFormula();
					} else {
						m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(super.getTrace().getSymbol(i).getTransitionFormula());
					}
					
				} else {
					m_TransFormulas[i] = super.getTrace().getSymbol(i).getTransitionFormula();
				}
			} else {
				if (super.getTrace().getSymbol(i) instanceof Call) {
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						m_TransFormulas[i] = super.getTrace().getSymbol(i).getTransitionFormula();
					} else {
						m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(super.getTrace().getSymbol(i).getTransitionFormula());
					}
					m_GlobalAssignmentTransFormulaAtCall.put(i, buildTransFormulaForStmtNotInUnsatCore(
							modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName())));
					m_OldVarsAssignmentTransFormulasAtCall.put(i, 
							buildTransFormulaForStmtNotInUnsatCore(
									modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName())));
				} else {
					m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(super.getTrace().getSymbol(i).getTransitionFormula());
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
				new HashSet<TermVariable>(), 
				tf.getBranchEncoders(),
				tf.isInfeasible(),
				tf.getClosedFormula());
	}

	@Override
	public Set<Integer> callPositions() {
		return super.getTrace().computeCallPositions();
	}

	@Override
	protected TransFormula getFormulaFromValidNonCallPos(int i) {
		return m_TransFormulas[i];
	}

	@Override
	protected TransFormula getLocalVarAssignmentFromValidPos(int i) {
		return m_TransFormulas[i];
	}

	@Override
	protected TransFormula getGlobalVarAssignmentFromValidPos(int i) {
		return m_GlobalAssignmentTransFormulaAtCall.get(i);
	}

	@Override
	protected TransFormula getOldVarAssignmentFromValidPos(int i) {
		return m_OldVarsAssignmentTransFormulasAtCall.get(i);
	}

}
