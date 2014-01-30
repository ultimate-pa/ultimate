package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.util.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;


/**
 * Class for computing the relevant transformulas of a trace with unsatisfiable core.
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class RelevantTransFormulas extends NestedFormulas<TransFormula, IPredicate> {
	
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
	
	private final static boolean s_ComputeSumSizeFormulasInUnsatCore = false;
	
	/**
	 * Sum of the size of all formulas that are in the unsatisfiable core.
	 */
	private int m_SumSizeFormulasInUnsatCore = 0;
	private int m_SumSizeFormulasNotInUnsatCore = 0; 
	
	public RelevantTransFormulas(NestedWord<CodeBlock> nestedTrace,
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			Set<CodeBlock> unsat_core,
			ModifiableGlobalVariableManager modGlobalVarManager,
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			boolean[] oldVarAssignmentAtCallInUnsatCore,
			SmtManager smtManager) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		m_TransFormulas = new TransFormula[nestedTrace.length()];
		m_GlobalAssignmentTransFormulaAtCall = new HashMap<Integer, TransFormula>();
		m_OldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, TransFormula>();
		m_SmtManager = smtManager;
		generateRelevantTransFormulas(unsat_core, localVarAssignmentsAtCallInUnsatCore, 
				oldVarAssignmentAtCallInUnsatCore, modGlobalVarManager);
		
	}
	
	public RelevantTransFormulas(NestedWord<CodeBlock> nestedTrace,
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			Set<Term> unsat_core,
			ModifiableGlobalVariableManager modGlobalVarManager,
			SmtManager smtManager,
			AnnotateAndAsserterConjuncts aac) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		m_TransFormulas = new TransFormula[nestedTrace.length()];
		m_GlobalAssignmentTransFormulaAtCall = new HashMap<Integer, TransFormula>();
		m_OldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, TransFormula>();
		m_SmtManager = smtManager;
		generateRelevantTransFormulas(unsat_core, modGlobalVarManager, aac);
	}
	
	private void generateRelevantTransFormulas(Set<CodeBlock> unsat_core, 
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			boolean[] oldVarAssignmentAtCallInUnsatCore,
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
					if (oldVarAssignmentAtCallInUnsatCore[i]) {
						m_OldVarsAssignmentTransFormulasAtCall.put(i, modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()));
					} else {
						m_OldVarsAssignmentTransFormulasAtCall.put(i, 
								buildTransFormulaForStmtNotInUnsatCore(
										modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName())));
					}
					m_GlobalAssignmentTransFormulaAtCall.put(i, buildTransFormulaForStmtNotInUnsatCore(
							modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName())));
					
				} else {
					m_TransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(super.getTrace().getSymbol(i).getTransitionFormula());
				}
			}
		}
		
	}
	
	private void generateRelevantTransFormulas(Set<Term> unsat_core, 
			ModifiableGlobalVariableManager modGlobalVarManager,
			AnnotateAndAsserterConjuncts aac) {
		Map<Term, Term> annot2Original = aac.getAnnotated2Original();
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (super.getTrace().getSymbol(i) instanceof Call) {
				// 1. Local var assignment
				Term[] conjuncts_annot = PartialQuantifierElimination.getConjuncts(aac.getAnnotatedSsa().getLocalVarAssignment(i));
				Set<Term> conjunctsInUnsatCore = filterRelevantConjuncts(
						unsat_core, annot2Original, conjuncts_annot);
				m_TransFormulas[i]  = buildTransFormulaWithRelevantConjuncts(super.getTrace().getSymbol(i).getTransitionFormula(),
						conjunctsInUnsatCore.toArray(new Term[0]));
				// 2. Global Var assignment
				conjuncts_annot = PartialQuantifierElimination.getConjuncts(aac.getAnnotatedSsa().getGlobalVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjuncts(unsat_core, annot2Original, conjuncts_annot);
				m_GlobalAssignmentTransFormulaAtCall.put(i, buildTransFormulaWithRelevantConjuncts(
						modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()),
						conjunctsInUnsatCore.toArray(new Term[0])));
				// 3. Old Var Assignment
				conjuncts_annot = PartialQuantifierElimination.getConjuncts(aac.getAnnotatedSsa().getOldVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjuncts(unsat_core, annot2Original, conjuncts_annot);
				m_OldVarsAssignmentTransFormulasAtCall.put(i, buildTransFormulaWithRelevantConjuncts(
						modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()),
						conjunctsInUnsatCore.toArray(new Term[0])));
				
			} else {
				Term[] conjuncts_annot = PartialQuantifierElimination.getConjuncts(aac.getAnnotatedSsa().getFormulaFromNonCallPos(i));
				Set<Term> conjunctsInUnsatCore = filterRelevantConjuncts(
						unsat_core, annot2Original, conjuncts_annot);
				m_TransFormulas[i]  = buildTransFormulaWithRelevantConjuncts(super.getTrace().getSymbol(i).getTransitionFormula(),
						conjunctsInUnsatCore.toArray(new Term[0]));
			}
		}
		
	}

	/**
	 * Filters out the irrelevant conjuncts, i.e. all conjuncts that are
	 * not contained in the unsatisfiable core, are replaced by "true".
	 */
	private Set<Term> filterRelevantConjuncts(Set<Term> unsat_core,
			Map<Term, Term> annot2Original, Term[] conjuncts_annot) {
		Set<Term> conjunctsInUnsatCore = new HashSet<Term>(conjuncts_annot.length);
		for (int j = 0; j < conjuncts_annot.length; j++) {
			if (unsat_core.contains(conjuncts_annot[j])) {
				Term original = annot2Original.get(conjuncts_annot[j]);
				if (s_ComputeSumSizeFormulasInUnsatCore) {
					m_SumSizeFormulasInUnsatCore += (new DAGSize()).size(original);
				}
				conjunctsInUnsatCore.add(original);
			} else {
				if (s_ComputeSumSizeFormulasInUnsatCore) {
					Term original = annot2Original.get(conjuncts_annot[j]);
					m_SumSizeFormulasNotInUnsatCore += (new DAGSize()).size(original);
				}
			}
		}
		return conjunctsInUnsatCore;
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
	
	private TransFormula buildTransFormulaWithRelevantConjuncts(TransFormula tf, Term[] conjunctsInUnsatCore) {
		Term formula = Util.and(m_SmtManager.getScript(), conjunctsInUnsatCore);
		Set<TermVariable> freeVars = new HashSet<TermVariable>();
		Collections.addAll(freeVars, formula.getFreeVars());
		Map<BoogieVar, TermVariable> invars = new HashMap<BoogieVar, TermVariable>();
		Map<BoogieVar, TermVariable> outvars = new HashMap<BoogieVar, TermVariable>();
		for (BoogieVar bv : tf.getInVars().keySet()) {
			if (freeVars.contains(tf.getInVars().get(bv))) {
				invars.put(bv, tf.getInVars().get(bv));
			}
		}
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (tf.getOutVars().get(bv) != tf.getInVars().get(bv)) {
				outvars.put(bv, tf.getOutVars().get(bv));
			} else if (freeVars.contains(tf.getOutVars().get(bv))) {
				outvars.put(bv, tf.getOutVars().get(bv));
			}
		}
		Set<TermVariable> auxVars = new HashSet<TermVariable>();
		for (TermVariable tv : tf.getAuxVars()) {
			if (freeVars.contains(tv)) {
				auxVars.add(tv);
			}
		}
		Term closedFormula = TransFormula.computeClosedFormula(formula, invars, outvars, auxVars, m_SmtManager.getBoogie2Smt());
		
		return new TransFormula(formula,
				invars,
				outvars,
				auxVars, 
				tf.getBranchEncoders(),
				tf.isInfeasible(),
				closedFormula);
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
