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
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAssertConjunctsOfCodeBlocks.SplitEqualityMapping;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;


/**
 * Class for computing the relevant transformulas of a trace with unsatisfiable core.
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class RelevantTransFormulas extends NestedFormulas<UnmodifiableTransFormula, IPredicate> {
	
	/**
	 * If index i is an internal position or a return transition in the
	 * nested trace Term[i] represents the i-th statement.
	 * If index i is a call position Term[i] represents the assignment
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.
	 */
	private final UnmodifiableTransFormula[] mTransFormulas;
	
	/**
	 * Maps a call position to a formula that represents the assignment
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
	 * global variables modified by the called procedure.
	 */
	private final Map<Integer,UnmodifiableTransFormula> mGlobalAssignmentTransFormulaAtCall;
	
	/**
	 * Maps a call position to a formula that represents the assignment
	 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
	 * global variables modified by the called procedure.
	 */
	private final Map<Integer, UnmodifiableTransFormula> mOldVarsAssignmentTransFormulasAtCall;
	
	
	private final ManagedScript mScript;
	
	private final static boolean s_ComputeSumSizeFormulasInUnsatCore = false;
	
	/**
	 * Sum of the size of all formulas that are in the unsatisfiable core.
	 */
	private int mSumSizeFormulasInUnsatCore = 0;
	private final int mSumSizeFormulasNotInUnsatCore = 0;
	
	public RelevantTransFormulas(final NestedWord<? extends IAction> nestedTrace,
			final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts,
			final Set<IAction> unsat_core,
			final ModifiableGlobalVariableManager modGlobalVarManager,
			final boolean[] localVarAssignmentsAtCallInUnsatCore,
			final boolean[] oldVarAssignmentAtCallInUnsatCore,
			final ManagedScript script) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mTransFormulas = new UnmodifiableTransFormula[nestedTrace.length()];
		mGlobalAssignmentTransFormulaAtCall = new HashMap<Integer, UnmodifiableTransFormula>();
		mOldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, UnmodifiableTransFormula>();
		mScript = script;
		generateRelevantTransFormulas(unsat_core, localVarAssignmentsAtCallInUnsatCore,
				oldVarAssignmentAtCallInUnsatCore, modGlobalVarManager);
		
	}
	
	public RelevantTransFormulas(final NestedWord<? extends IAction> nestedTrace,
			final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts,
			final Set<Term> unsat_core,
			final ModifiableGlobalVariableManager modGlobalVarManager,
			final ManagedScript script,
			final AnnotateAndAsserter aaa,
			final AnnotateAndAssertConjunctsOfCodeBlocks aac) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mTransFormulas = new UnmodifiableTransFormula[nestedTrace.length()];
		mGlobalAssignmentTransFormulaAtCall = new HashMap<Integer, UnmodifiableTransFormula>();
		mOldVarsAssignmentTransFormulasAtCall = new HashMap<Integer, UnmodifiableTransFormula>();
		mScript = script;
		generateRelevantTransFormulas(unsat_core, modGlobalVarManager, aaa, aac);
	}
	
	private void generateRelevantTransFormulas(final Set<IAction> unsat_core,
			final boolean[] localVarAssignmentsAtCallInUnsatCore,
			final boolean[] oldVarAssignmentAtCallInUnsatCore,
			final ModifiableGlobalVariableManager modGlobalVarManager) {
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
	
	private void generateRelevantTransFormulas(final Set<Term> unsat_core,
			final ModifiableGlobalVariableManager modGlobalVarManager,
			final AnnotateAndAsserter aaa,
			final AnnotateAndAssertConjunctsOfCodeBlocks aac) {
		final Map<Term, Term> annot2Original = aac.getAnnotated2Original();
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (super.getTrace().getSymbol(i) instanceof Call) {
				// 1. Local var assignment
				Term[] conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getLocalVarAssignment(i));
				Set<Term> conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(
						unsat_core, annot2Original, conjuncts_annot, aac.getSplitEqualityMapping());
				mTransFormulas[i]  = buildTransFormulaWithRelevantConjuncts(((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula(),
						conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()]));
				// 2. Global Var assignment
				conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getGlobalVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsat_core, annot2Original, conjuncts_annot,
						aac.getSplitEqualityMapping());
				mGlobalAssignmentTransFormulaAtCall.put(i, buildTransFormulaWithRelevantConjuncts(
						modGlobalVarManager.getGlobalVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()),
						conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()])));
				// 3. Old Var Assignment
				conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getOldVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsat_core, annot2Original, conjuncts_annot,
						aac.getSplitEqualityMapping());
				mOldVarsAssignmentTransFormulasAtCall.put(i, buildTransFormulaWithRelevantConjuncts(
						modGlobalVarManager.getOldVarsAssignment(((Call)super.getTrace().getSymbol(i)).getCallStatement().getMethodName()),
						conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()])));
			} else {
				final Term[] conjuncts_annot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getFormulaFromNonCallPos(i));
				final Set<Term> conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(
						unsat_core, annot2Original, conjuncts_annot, aac.getSplitEqualityMapping());
				mTransFormulas[i]  = buildTransFormulaWithRelevantConjuncts(((CodeBlock) super.getTrace().getSymbol(i)).getTransitionFormula(),
						conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()]));
			}
		}
		
	}

	/**
	 * Filters out the irrelevant conjuncts, and restore equalities, if possible. I.e. if there are two inequalities in
	 * the unsat core which belong together, then replace them by one equality.
	 */
	private Set<Term> filterRelevantConjunctsAndRestoreEqualities(final Set<Term> unsat_core,
			final Map<Term, Term> annot2Original, final Term[] conjuncts_annot,
			final SplitEqualityMapping sem) {
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
	
	private UnmodifiableTransFormula buildTransFormulaForStmtNotInUnsatCore(final UnmodifiableTransFormula tf) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null,
				tf.getBranchEncoders().isEmpty(), tf.getBranchEncoders(), true);
		for (final IProgramVar bv : tf.getAssignedVars()) {
			if (tf.getOutVars().containsKey(bv)) {
				tfb.addOutVar(bv, tf.getOutVars().get(bv));
			}
		}
		tfb.setFormula(mScript.getScript().term("true"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mScript);
	}
	
	private UnmodifiableTransFormula buildTransFormulaWithRelevantConjuncts(
			final UnmodifiableTransFormula tf, final Term[] conjunctsInUnsatCore) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(
				null, null, false, null, false);
		
		final Term formula = Util.and(mScript.getScript(), conjunctsInUnsatCore);
		final Set<TermVariable> freeVars = new HashSet<TermVariable>();
		Collections.addAll(freeVars, formula.getFreeVars());
		for (final IProgramVar bv : tf.getInVars().keySet()) {
			if (freeVars.contains(tf.getInVars().get(bv))) {
				tfb.addInVar(bv, tf.getInVars().get(bv));
			}
		}
		for (final IProgramVar bv : tf.getOutVars().keySet()) {
			if (tf.getOutVars().get(bv) != tf.getInVars().get(bv)) {
				tfb.addOutVar(bv, tf.getOutVars().get(bv));
			} else if (freeVars.contains(tf.getOutVars().get(bv))) {
				tfb.addOutVar(bv, tf.getOutVars().get(bv));
			}
		}
		final Set<TermVariable> auxVars = new HashSet<>();
		for (final TermVariable auxVar : tf.getAuxVars()) {
			if (freeVars.contains(auxVar)) {
				auxVars.add(auxVar);
			}
		}
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, mScript);
		return tfb.finishConstruction(mScript);
	}

	@Override
	protected UnmodifiableTransFormula getFormulaFromValidNonCallPos(final int i) {
		return mTransFormulas[i];
	}

	@Override
	protected UnmodifiableTransFormula getLocalVarAssignmentFromValidPos(final int i) {
		return mTransFormulas[i];
	}

	@Override
	protected UnmodifiableTransFormula getGlobalVarAssignmentFromValidPos(final int i) {
		return mGlobalAssignmentTransFormulaAtCall.get(i);
	}

	@Override
	protected UnmodifiableTransFormula getOldVarAssignmentFromValidPos(final int i) {
		return mOldVarsAssignmentTransFormulasAtCall.get(i);
	}
}
