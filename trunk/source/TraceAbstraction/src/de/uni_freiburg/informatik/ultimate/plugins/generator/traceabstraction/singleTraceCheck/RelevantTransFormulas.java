/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAssertConjunctsOfCodeBlocks.SplitEqualityMapping;
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
	private final TransFormula[] mTransFormulas;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer,TransFormula> mGlobalAssignmentTransFormulaAtCall;
	
	/**
	 * Maps a call position to a formula that represents the assignment 
	 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
	 * global variables modified by the called procedure.  
	 */
	private final Map<Integer, TransFormula> mOldVarsAssignmentTransFormulasAtCall;
	
	
	private final Boogie2SMT mBoogie2Smt;
	
	private final static boolean s_ComputeSumSizeFormulasInUnsatCore = false;
	
	/**
	 * Sum of the size of all formulas that are in the unsatisfiable core.
	 */
	private int mSumSizeFormulasInUnsatCore = 0;
	private final int mSumSizeFormulasNotInUnsatCore = 0; 
	
	public RelevantTransFormulas(NestedWord<? extends IAction> nestedTrace,
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			Set<IAction> unsat_core,
			ModifiableGlobalVariableManager modGlobalVarManager,
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			boolean[] oldVarAssignmentAtCallInUnsatCore,
			Boogie2SMT boogie2smt) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mTransFormulas = new TransFormula[nestedTrace.length()];
		mGlobalAssignmentTransFormulaAtCall = new HashMap<Integer, TransFormula>();
		mOldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, TransFormula>();
		mBoogie2Smt = boogie2smt;
		generateRelevantTransFormulas(unsat_core, localVarAssignmentsAtCallInUnsatCore, 
				oldVarAssignmentAtCallInUnsatCore, modGlobalVarManager);
		
	}
	
	public RelevantTransFormulas(NestedWord<? extends IAction> nestedTrace,
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			Set<Term> unsat_core,
			ModifiableGlobalVariableManager modGlobalVarManager,
			Boogie2SMT boogie2smt,
			AnnotateAndAsserter aaa,
			AnnotateAndAssertConjunctsOfCodeBlocks aac) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mTransFormulas = new TransFormula[nestedTrace.length()];
		mGlobalAssignmentTransFormulaAtCall = new HashMap<Integer, TransFormula>();
		mOldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, TransFormula>();
		mBoogie2Smt = boogie2smt;
		generateRelevantTransFormulas(unsat_core, modGlobalVarManager, aaa, aac);
	}
	
	private void generateRelevantTransFormulas(Set<IAction> unsat_core, 
			boolean[] localVarAssignmentsAtCallInUnsatCore,
			boolean[] oldVarAssignmentAtCallInUnsatCore,
			ModifiableGlobalVariableManager modGlobalVarManager) {
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (unsat_core.contains(super.getTrace().getSymbol(i))) {
				if (super.getTrace().getSymbol(i) instanceof ICallAction) {
					final ICallAction call = (ICallAction) super.getTrace().getSymbol(i);
					mGlobalAssignmentTransFormulaAtCall.put(i,
							modGlobalVarManager.getGlobalVarsAssignment(call.getSucceedingProcedure()));
					mOldVarsAssignmentTransFormulasAtCall.put(i, 
							modGlobalVarManager.getOldVarsAssignment(call.getSucceedingProcedure()));
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						mTransFormulas[i] = call.getLocalVarsAssignment();
					} else {
						mTransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(call.getLocalVarsAssignment());
					}
				} else {
					mTransFormulas[i] = ((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula();
				}
			} else {
				if (super.getTrace().getSymbol(i) instanceof Call) {
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						mTransFormulas[i] = ((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula();
					} else {
						mTransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula());
					}
					if (oldVarAssignmentAtCallInUnsatCore[i]) {
						mOldVarsAssignmentTransFormulasAtCall.put(i, modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()));
					} else {
						mOldVarsAssignmentTransFormulasAtCall.put(i, 
								buildTransFormulaForStmtNotInUnsatCore(
										modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName())));
					}
					mGlobalAssignmentTransFormulaAtCall.put(i, buildTransFormulaForStmtNotInUnsatCore(
							modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName())));
					
				} else {
					mTransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula());
				}
			}
		}
		
	}
	
	private void generateRelevantTransFormulas(Set<Term> unsat_core, 
			ModifiableGlobalVariableManager modGlobalVarManager,
			AnnotateAndAsserter aaa,
			AnnotateAndAssertConjunctsOfCodeBlocks aac) {
		final Map<Term, Term> annot2Original = aac.getAnnotated2Original();
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (super.getTrace().getSymbol(i) instanceof Call) {
				// 1. Local var assignment
				Term[] conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getLocalVarAssignment(i));
				Set<Term> conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(
						unsat_core, annot2Original, conjuncts_annot, aac.getSplitEqualityMapping());
				mTransFormulas[i]  = buildTransFormulaWithRelevantConjuncts(((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula(),
						conjunctsInUnsatCore.toArray(new Term[0]));
				// 2. Global Var assignment
				conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getGlobalVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsat_core, annot2Original, conjuncts_annot,
						aac.getSplitEqualityMapping());
				mGlobalAssignmentTransFormulaAtCall.put(i, buildTransFormulaWithRelevantConjuncts(
						modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()),
						conjunctsInUnsatCore.toArray(new Term[0])));
				// 3. Old Var Assignment
				conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getOldVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsat_core, annot2Original, conjuncts_annot,
						aac.getSplitEqualityMapping());
				mOldVarsAssignmentTransFormulasAtCall.put(i, buildTransFormulaWithRelevantConjuncts(
						modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()),
						conjunctsInUnsatCore.toArray(new Term[0])));
			} else {
				final Term[] conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getFormulaFromNonCallPos(i));
				final Set<Term> conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(
						unsat_core, annot2Original, conjuncts_annot, aac.getSplitEqualityMapping());
				mTransFormulas[i]  = buildTransFormulaWithRelevantConjuncts(((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula(),
						conjunctsInUnsatCore.toArray(new Term[0]));
			}
		}
		
	}

	/**
	 * Filters out the irrelevant conjuncts, and restore equalities, if possible. I.e. if there are two inequalities in
	 * the unsat core which belong together, then replace them by one equality.
	 */
	private Set<Term> filterRelevantConjunctsAndRestoreEqualities(Set<Term> unsat_core,
			Map<Term, Term> annot2Original, Term[] conjuncts_annot,
			SplitEqualityMapping sem) {
		final Set<Term> conjunctsInUnsatCore = new HashSet<Term>(conjuncts_annot.length);
		final Set<Term> conjuncts_annotInequalitiesSuccRestored = new HashSet<Term>();
		
		for (int j = 0; j < conjuncts_annot.length; j++) {
			// Check current annotated conjunct if and only if we didn't have restored its inequality 
			if (!conjuncts_annotInequalitiesSuccRestored.contains(conjuncts_annot[j])) {
				if (sem.getInequality2CorrespondingInequality().containsKey(conjuncts_annot[j])) {
					final Term firstInequality = conjuncts_annot[j];
					final Term secondInequality =  sem.getInequality2CorrespondingInequality().get(firstInequality);
					// Restore the equality from firstInequality and secondInequality if both are contained in the unsat core
					if (unsat_core.contains(firstInequality) && unsat_core.contains(secondInequality)) {
						conjuncts_annotInequalitiesSuccRestored.add(firstInequality);
						conjuncts_annotInequalitiesSuccRestored.add(secondInequality);
						final Term original = sem.getInequality2OriginalEquality().get(firstInequality);
						
						if (s_ComputeSumSizeFormulasInUnsatCore) {
							mSumSizeFormulasInUnsatCore += (new DAGSize()).size(original);
						}
						conjunctsInUnsatCore.add(original);
					} else if (unsat_core.contains(firstInequality)) {
						final Term original = annot2Original.get(firstInequality);
						if (s_ComputeSumSizeFormulasInUnsatCore) {
							mSumSizeFormulasInUnsatCore += (new DAGSize()).size(original);
						}
						conjunctsInUnsatCore.add(original);
					}
				} else {
					if (unsat_core.contains(conjuncts_annot[j])) {
						final Term original = annot2Original.get(conjuncts_annot[j]);
						if (s_ComputeSumSizeFormulasInUnsatCore) {
							mSumSizeFormulasInUnsatCore += (new DAGSize()).size(original);
						}
						conjunctsInUnsatCore.add(original);
					}
				}
			}
		}
		return conjunctsInUnsatCore;
	}
	
	private TransFormula buildTransFormulaForStmtNotInUnsatCore(TransFormula tf) {
		final Map<IProgramVar, TermVariable> outvars = new HashMap<IProgramVar, TermVariable>();
		for (final IProgramVar bv : tf.getAssignedVars()) {
			if (tf.getOutVars().containsKey(bv)) {
				outvars.put(bv, tf.getOutVars().get(bv));
			}
		}
		
		return new TransFormula(mBoogie2Smt.getScript().term("true"),
				new HashMap<IProgramVar, TermVariable>(),
				outvars,
				Collections.emptyMap(), 
				tf.getBranchEncoders(),
				tf.isInfeasible(),
				tf.getClosedFormula());
	}
	
	private TransFormula buildTransFormulaWithRelevantConjuncts(TransFormula tf, Term[] conjunctsInUnsatCore) {
		final Term formula = Util.and(mBoogie2Smt.getScript(), conjunctsInUnsatCore);
		final Set<TermVariable> freeVars = new HashSet<TermVariable>();
		Collections.addAll(freeVars, formula.getFreeVars());
		final Map<IProgramVar, TermVariable> invars = new HashMap<IProgramVar, TermVariable>();
		final Map<IProgramVar, TermVariable> outvars = new HashMap<IProgramVar, TermVariable>();
		for (final IProgramVar bv : tf.getInVars().keySet()) {
			if (freeVars.contains(tf.getInVars().get(bv))) {
				invars.put(bv, tf.getInVars().get(bv));
			}
		}
		for (final IProgramVar bv : tf.getOutVars().keySet()) {
			if (tf.getOutVars().get(bv) != tf.getInVars().get(bv)) {
				outvars.put(bv, tf.getOutVars().get(bv));
			} else if (freeVars.contains(tf.getOutVars().get(bv))) {
				outvars.put(bv, tf.getOutVars().get(bv));
			}
		}
		final Map<TermVariable, Term> auxVars = new HashMap<TermVariable, Term>();
		for (final Entry<TermVariable, Term> entry : tf.getAuxVars().entrySet()) {
			if (freeVars.contains(entry.getKey())) {
				auxVars.put(entry.getKey(), entry.getValue());
			}
		}
		final Term closedFormula = TransFormula.computeClosedFormula(formula, invars, outvars, auxVars, mBoogie2Smt);
		
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
		return mTransFormulas[i];
	}

	@Override
	protected TransFormula getLocalVarAssignmentFromValidPos(int i) {
		return mTransFormulas[i];
	}

	@Override
	protected TransFormula getGlobalVarAssignmentFromValidPos(int i) {
		return mGlobalAssignmentTransFormulaAtCall.get(i);
	}

	@Override
	protected TransFormula getOldVarAssignmentFromValidPos(int i) {
		return mOldVarsAssignmentTransFormulasAtCall.get(i);
	}
}
