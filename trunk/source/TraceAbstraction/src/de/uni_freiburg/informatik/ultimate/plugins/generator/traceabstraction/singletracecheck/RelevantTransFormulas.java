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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.OldVarsAssignmentCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.AnnotateAndAssertConjunctsOfCodeBlocks.SplitEqualityMapping;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * Class for computing the relevant transformulas of a trace with unsatisfiable core.
 *
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class RelevantTransFormulas extends NestedFormulas<UnmodifiableTransFormula, IPredicate> {

	private static final boolean COMPUTE_SUM_SIZE_FORMULAS_IN_UNSAT_CORE = false;

	/**
	 * If index i is an internal position or a return transition in the nested trace Term[i] represents the i-th
	 * statement. If index i is a call position Term[i] represents the assignment
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the global variables modified by the called
	 * procedure.
	 */
	private final UnmodifiableTransFormula[] mTransFormulas;

	/**
	 * Maps a call position to a formula that represents the assignment {@code g_1,...,g_n := old(g_1),...,old(g_n)}
	 * where g_1,...,g_n are the global variables modified by the called procedure.
	 */
	private final Map<Integer, UnmodifiableTransFormula> mGlobalAssignmentTransFormulaAtCall;

	/**
	 * Maps a call position to a formula that represents the assignment {@code old(g_1),...,old(g_n) := g_1,...,g_n}
	 * where g_1,...,g_n are the global variables modified by the called procedure.
	 */
	private final Map<Integer, UnmodifiableTransFormula> mOldVarsAssignmentTransFormulasAtCall;

	private final ManagedScript mScript;

	/**
	 * Sum of the size of all formulas that are in the unsatisfiable core.
	 */
	private int mSumSizeFormulasInUnsatCore = 0;

	public RelevantTransFormulas(final NestedWord<? extends IAction> nestedTrace, final IPredicate precondition,
			final IPredicate postcondition, final SortedMap<Integer, IPredicate> pendingContexts,
			final Set<IAction> unsatCore, final OldVarsAssignmentCache oldVarsAssignmentCache,
			final boolean[] localVarAssignmentsAtCallInUnsatCore, final boolean[] oldVarAssignmentAtCallInUnsatCore,
			final ManagedScript script) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mTransFormulas = new UnmodifiableTransFormula[nestedTrace.length()];
		mGlobalAssignmentTransFormulaAtCall = new HashMap<>();
		mOldVarsAssignmentTransFormulasAtCall = new HashMap<>();
		mScript = script;
		generateRelevantTransFormulas(unsatCore, localVarAssignmentsAtCallInUnsatCore,
				oldVarAssignmentAtCallInUnsatCore, oldVarsAssignmentCache);

	}

	public RelevantTransFormulas(final NestedWord<? extends IAction> nestedTrace, final IPredicate precondition,
			final IPredicate postcondition, final SortedMap<Integer, IPredicate> pendingContexts,
			final Set<Term> unsatCore, final OldVarsAssignmentCache modGlobalVarManager, final ManagedScript script,
			final AnnotateAndAsserter aaa, final AnnotateAndAssertConjunctsOfCodeBlocks aac) {
		super(nestedTrace, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mTransFormulas = new UnmodifiableTransFormula[nestedTrace.length()];
		mGlobalAssignmentTransFormulaAtCall = new HashMap<>();
		mOldVarsAssignmentTransFormulasAtCall = new HashMap<>();
		mScript = script;
		generateRelevantTransFormulas(unsatCore, modGlobalVarManager, aaa, aac);
	}

	private void generateRelevantTransFormulas(final Set<IAction> unsatCore,
			final boolean[] localVarAssignmentsAtCallInUnsatCore, final boolean[] oldVarAssignmentAtCallInUnsatCore,
			final OldVarsAssignmentCache oldVarsAssignmentCache) {
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (unsatCore.contains(super.getTrace().getSymbol(i))) {
				if (super.getTrace().getSymbol(i) instanceof ICallAction) {
					final ICallAction call = (ICallAction) super.getTrace().getSymbol(i);
					mGlobalAssignmentTransFormulaAtCall.put(i,
							oldVarsAssignmentCache.getGlobalVarsAssignment(call.getSucceedingProcedure()));
					mOldVarsAssignmentTransFormulasAtCall.put(i,
							oldVarsAssignmentCache.getOldVarsAssignment(call.getSucceedingProcedure()));
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						mTransFormulas[i] = call.getLocalVarsAssignment();
					} else {
						mTransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(call.getLocalVarsAssignment());
					}
				} else {
					mTransFormulas[i] = ((IAction) super.getTrace().getSymbol(i)).getTransformula();
				}
			} else {
				if (super.getTrace().getSymbol(i) instanceof ICallAction) {
					if (localVarAssignmentsAtCallInUnsatCore[i]) {
						mTransFormulas[i] = ((IAction) super.getTrace().getSymbol(i)).getTransformula();
					} else {
						mTransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(
								((IAction) super.getTrace().getSymbol(i)).getTransformula());
					}
					if (oldVarAssignmentAtCallInUnsatCore[i]) {
						mOldVarsAssignmentTransFormulasAtCall.put(i, oldVarsAssignmentCache.getOldVarsAssignment(
								((ICallAction) super.getTrace().getSymbol(i)).getSucceedingProcedure()));
					} else {
						mOldVarsAssignmentTransFormulasAtCall.put(i,
								buildTransFormulaForStmtNotInUnsatCore(oldVarsAssignmentCache.getOldVarsAssignment(
										((ICallAction) super.getTrace().getSymbol(i)).getSucceedingProcedure())));
					}
					mGlobalAssignmentTransFormulaAtCall.put(i,
							buildTransFormulaForStmtNotInUnsatCore(oldVarsAssignmentCache.getGlobalVarsAssignment(
									((ICallAction) super.getTrace().getSymbol(i)).getSucceedingProcedure())));

				} else {
					mTransFormulas[i] = buildTransFormulaForStmtNotInUnsatCore(
							((IAction) super.getTrace().getSymbol(i)).getTransformula());
				}
			}
		}

	}

	private void generateRelevantTransFormulas(final Set<Term> unsatCore,
			final OldVarsAssignmentCache modGlobalVarManager, final AnnotateAndAsserter aaa,
			final AnnotateAndAssertConjunctsOfCodeBlocks aac) {
		final Map<Term, Term> annot2Original = aac.getAnnotated2Original();
		for (int i = 0; i < super.getTrace().length(); i++) {
			if (super.getTrace().getSymbol(i) instanceof ICallAction) {
				// 1. Local var assignment
				Term[] conjunctsAnnot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getLocalVarAssignment(i));
				Set<Term> conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsatCore, annot2Original,
						conjunctsAnnot, aac.getSplitEqualityMapping());
				mTransFormulas[i] = buildTransFormulaWithRelevantConjuncts(
						((IAction) super.getTrace().getSymbol(i)).getTransformula(),
						conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()]));
				// 2. Global Var assignment
				conjunctsAnnot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getGlobalVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsatCore, annot2Original,
						conjunctsAnnot, aac.getSplitEqualityMapping());
				mGlobalAssignmentTransFormulaAtCall.put(i,
						buildTransFormulaWithRelevantConjuncts(
								modGlobalVarManager.getGlobalVarsAssignment(
										((ICallAction) super.getTrace().getSymbol(i)).getSucceedingProcedure()),
								conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()])));
				// 3. Old Var Assignment
				conjunctsAnnot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getOldVarAssignment(i));
				conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsatCore, annot2Original,
						conjunctsAnnot, aac.getSplitEqualityMapping());
				mOldVarsAssignmentTransFormulasAtCall.put(i,
						buildTransFormulaWithRelevantConjuncts(
								modGlobalVarManager.getOldVarsAssignment(
										((ICallAction) super.getTrace().getSymbol(i)).getSucceedingProcedure()),
								conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()])));
			} else {
				final Term[] conjunctsAnnot = SmtUtils.getConjuncts(aaa.getAnnotatedSsa().getFormulaFromNonCallPos(i));
				final Set<Term> conjunctsInUnsatCore = filterRelevantConjunctsAndRestoreEqualities(unsatCore,
						annot2Original, conjunctsAnnot, aac.getSplitEqualityMapping());
				mTransFormulas[i] =
						buildTransFormulaWithRelevantConjuncts(super.getTrace().getSymbol(i).getTransformula(),
								conjunctsInUnsatCore.toArray(new Term[conjunctsInUnsatCore.size()]));
			}
		}

	}

	/**
	 * Filters out the irrelevant conjuncts, and restore equalities, if possible. I.e. if there are two inequalities in
	 * the unsat core which belong together, then replace them by one equality.
	 */
	private Set<Term> filterRelevantConjunctsAndRestoreEqualities(final Set<Term> unsatCore,
			final Map<Term, Term> annot2Original, final Term[] conjunctsAnnot, final SplitEqualityMapping sem) {
		final Set<Term> conjunctsInUnsatCore = new HashSet<>(conjunctsAnnot.length);
		final Set<Term> conjunctsAnnotInequalitiesSuccRestored = new HashSet<>();

		for (int j = 0; j < conjunctsAnnot.length; j++) {
			// Check current annotated conjunct if and only if we didn't have restored its inequality
			if (!conjunctsAnnotInequalitiesSuccRestored.contains(conjunctsAnnot[j])) {
				if (sem.getInequality2CorrespondingInequality().containsKey(conjunctsAnnot[j])) {
					final Term firstInequality = conjunctsAnnot[j];
					final Term secondInequality = sem.getInequality2CorrespondingInequality().get(firstInequality);
					// Restore the equality from firstInequality and secondInequality if both are contained in the unsat
					// core
					if (unsatCore.contains(firstInequality) && unsatCore.contains(secondInequality)) {
						conjunctsAnnotInequalitiesSuccRestored.add(firstInequality);
						conjunctsAnnotInequalitiesSuccRestored.add(secondInequality);
						final Term original = sem.getInequality2OriginalEquality().get(firstInequality);

						if (COMPUTE_SUM_SIZE_FORMULAS_IN_UNSAT_CORE) {
							mSumSizeFormulasInUnsatCore += new DAGSize().size(original);
						}
						conjunctsInUnsatCore.add(original);
					} else if (unsatCore.contains(firstInequality)) {
						final Term original = annot2Original.get(firstInequality);
						if (COMPUTE_SUM_SIZE_FORMULAS_IN_UNSAT_CORE) {
							mSumSizeFormulasInUnsatCore += new DAGSize().size(original);
						}
						conjunctsInUnsatCore.add(original);
					}
				} else {
					if (unsatCore.contains(conjunctsAnnot[j])) {
						final Term original = annot2Original.get(conjunctsAnnot[j]);
						if (COMPUTE_SUM_SIZE_FORMULAS_IN_UNSAT_CORE) {
							mSumSizeFormulasInUnsatCore += new DAGSize().size(original);
						}
						conjunctsInUnsatCore.add(original);
					}
				}
			}
		}
		return conjunctsInUnsatCore;
	}

	private UnmodifiableTransFormula buildTransFormulaForStmtNotInUnsatCore(final UnmodifiableTransFormula tf) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null,
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

	private UnmodifiableTransFormula buildTransFormulaWithRelevantConjuncts(final UnmodifiableTransFormula tf,
			final Term[] conjunctsInUnsatCore) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, false, null, false, null, false);

		final Term formula = SmtUtils.and(mScript.getScript(), conjunctsInUnsatCore);
		final Set<TermVariable> freeVars = new HashSet<>();
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

		final Set<IProgramConst> nonTheoryConstants = tf.getNonTheoryConsts();
		TransFormulaUtils.addConstantsIfInFormula(tfb, formula, nonTheoryConstants);
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
