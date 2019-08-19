/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.GlobalBoogieVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.OldVarsAssignmentCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class IncrementalHoareTripleChecker implements IHoareTripleChecker {

	private static final String MSG_UNEXPECTED_QUICKCHECK_RESULT = "unexpected quickcheck result";
	private static final String MSG_WRONG_KIND_OF_ACTION = "Wrong kind of action";
	private static final String ANNOT_NAMED = ":named";
	public static final boolean UNLET_TERMS = true;
	protected static final String ID_PRECONDITION = "precondition";
	protected static final String ID_PRECONDITION_NON_MOD_GLOBAL_EQUALITY = "precondNonModGlobalEquality";
	protected static final String ID_TRANSITION_MODIFIABLE_GLOBAL_EQUALITY = "modifiableVarEquality";
	protected static final String ID_TRANSITION_FORMULA = "codeBlock";
	protected static final String ID_LOCAL_VARS_ASSIGNMENT = "localVarsAssignment";
	protected static final String ID_HIERACHICAL_PRECONDITION = "hierarchicalPrecondition";
	protected static final String ID_NEGATED_POSTCONDITION = "negatedPostcondition";
	private static final String MSG_START_EDGE_CHECK = "starting to check validity of Hoare triples";
	private static final String MSG_END_EDGE_CHECK = "finished to check validity of Hoare triples";

	protected final ManagedScript mManagedScript;
	protected final ModifiableGlobalsTable mModifiableGlobalVariableManager;
	private final OldVarsAssignmentCache mOldVarsAssignmentCache;

	private IPredicate mAssertedPrecond;
	protected IPredicate mAssertedHier;
	protected IAction mAssertedAction;
	private IPredicate mAssertedPostcond;
	private ScopedHashMap<IProgramVar, Term> mHierConstants;
	public final boolean mUseNamedTerms = true;

	protected final HoareTripleCheckerStatisticsGenerator mEdgeCheckerBenchmark;
	private final boolean mConstructCounterexamples;
	private ProgramState<Term> mCounterexampleStatePrecond;
	private ProgramState<Term> mCounterexampleStatePostcond;

	/**
	 * @param constructCounterexamples
	 *            if a Hoare triple was invalid, then construct a pair of {@link ProgramState}s. This pair constitutes a
	 *            counterexample to validity. One {@link ProgramState} represents a state before executing the
	 *            transition, the other represents a state after executing the transition.
	 *
	 *            TODO: Return a third {@link ProgramState} in counterexamples to validity of return transitions (will
	 *            represent state before call)
	 */
	public IncrementalHoareTripleChecker(final CfgSmtToolkit csToolkit, final boolean constructCounterexamples) {
		mManagedScript = csToolkit.getManagedScript();
		mModifiableGlobalVariableManager = csToolkit.getModifiableGlobalsTable();
		mOldVarsAssignmentCache = csToolkit.getOldVarsAssignmentCache();
		mEdgeCheckerBenchmark = new HoareTripleCheckerStatisticsGenerator();
		mConstructCounterexamples = constructCounterexamples;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mEdgeCheckerBenchmark;
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		final LBool quickCheckTrans = prepareAssertionStackAndAddTransition(act);
		if (quickCheckTrans == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckLinPred = prepareAssertionStackAndAddPrecondition(pre);
		if (quickCheckLinPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckPostcond = prepareAssertionStackAndAddPostcond(post);
		if (quickCheckPostcond == LBool.UNSAT) {
			return Validity.VALID;
		}
		assert quickCheckPostcond == LBool.UNKNOWN || quickCheckPostcond == null : MSG_UNEXPECTED_QUICKCHECK_RESULT;
		assert mAssertedPrecond == pre && mAssertedHier == null && mAssertedAction == act && mAssertedPostcond == post;
		return checkValidity();
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
		final LBool quickCheckTrans = prepareAssertionStackAndAddTransition(act);
		if (quickCheckTrans == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckLinPred = prepareAssertionStackAndAddPrecondition(pre);
		if (quickCheckLinPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckPostcond = prepareAssertionStackAndAddPostcond(post);
		if (quickCheckPostcond == LBool.UNSAT) {
			return Validity.VALID;
		}
		assert quickCheckPostcond == LBool.UNKNOWN || quickCheckPostcond == null : MSG_UNEXPECTED_QUICKCHECK_RESULT;
		assert mAssertedPrecond == pre && mAssertedHier == null && mAssertedAction == act && mAssertedPostcond == post;
		return checkValidity();
	}

	@Override
	public Validity checkReturn(final IPredicate linPre, final IPredicate hierPre, final IReturnAction act,
			final IPredicate postcond) {
		final LBool quickCheckTrans = prepareAssertionStackAndAddTransition(act);
		if (quickCheckTrans == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckLinPred = prepareAssertionStackAndAddPrecondition(linPre);
		if (quickCheckLinPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckHierPred = prepareAssertionStackAndAddHierpred(hierPre);
		if (quickCheckHierPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheckPostcond = prepareAssertionStackAndAddPostcond(postcond);
		if (quickCheckPostcond == LBool.UNSAT) {
			return Validity.VALID;
		}
		assert quickCheckPostcond == LBool.UNKNOWN || quickCheckPostcond == null : MSG_UNEXPECTED_QUICKCHECK_RESULT;
		assert mAssertedPrecond == linPre && mAssertedHier == hierPre && mAssertedAction == act
				&& mAssertedPostcond == postcond;
		return checkValidity();
	}

	protected LBool prepareAssertionStackAndAddTransition(final IAction act) {
		if (mAssertedAction != act) {
			if (mAssertedAction != null) {
				if (mAssertedPrecond != null) {
					if (mAssertedPostcond != null) {
						unAssertPostcondition();
					}
					if (mAssertedHier != null) {
						unAssertHierPred();
					}
					unAssertPrecondition();
				}
				unAssertCodeBlock();
			}
			final LBool quickCheck = assertCodeBlock(act);
			return quickCheck;
		}
		return null;
	}

	protected LBool prepareAssertionStackAndAddPrecondition(final IPredicate precond) {
		if (mAssertedPrecond != precond) {
			if (mAssertedPrecond != null) {
				if (mAssertedPostcond != null) {
					unAssertPostcondition();
				}
				if (mAssertedHier != null) {
					unAssertHierPred();
				}
				unAssertPrecondition();
			}
			final LBool quickCheck = assertPrecondition(precond);
			return quickCheck;
		}
		return null;
	}

	protected LBool prepareAssertionStackAndAddHierpred(final IPredicate hierpred) {
		if (mAssertedHier != hierpred) {
			if (mAssertedPostcond != null) {
				unAssertPostcondition();
			}
			if (mAssertedHier != null) {
				unAssertHierPred();
			}
			final LBool quickCheck = assertHierPred(hierpred);
			return quickCheck;
		}
		return null;
	}

	protected LBool prepareAssertionStackAndAddPostcond(final IPredicate postcond) {
		if (mAssertedPostcond != postcond) {
			if (mAssertedPostcond != null) {
				unAssertPostcondition();
			}
			final LBool quickCheck = assertPostcond(postcond);
			return quickCheck;
		}
		return null;
	}

	protected LBool assertPostcond(final IPredicate postcond) {
		if (mAssertedAction instanceof IInternalAction) {
			return assertPostcondInternal(postcond);
		} else if (mAssertedAction instanceof ICallAction) {
			return assertPostcondCall(postcond);
		} else if (mAssertedAction instanceof IReturnAction) {
			return assertPostcondReturn(postcond);
		} else {
			throw new AssertionError("unknown trans type");
		}
	}

	public void clearAssertionStack() {
		if (mAssertedPostcond != null) {
			unAssertPostcondition();
		}
		if (mAssertedPrecond != null) {
			unAssertPrecondition();
		}
		if (mAssertedHier != null) {
			unAssertHierPred();
		}
		if (mAssertedAction != null) {
			unAssertCodeBlock();
		}
	}

	@Override
	public void releaseLock() {
		clearAssertionStack();
	}

	private LBool assertPrecondition(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedAction != null : "Assert CodeBlock first";
		assert mAssertedPrecond == null : "precond already asserted";
		mAssertedPrecond = p;
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		Term predcondition = p.getClosedFormula();
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_PRECONDITION);
			predcondition = mManagedScript.annotate(this, predcondition, annot);
		}
		LBool quickCheck = mManagedScript.assertTerm(this, predcondition);
		final String predProc = mAssertedAction.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(predProc);
		final Collection<Term> oldVarEqualities =
				constructNonModOldVarsEquality(p.getVars(), modifiableGlobals, mManagedScript, this);
		if (!oldVarEqualities.isEmpty()) {
			Term nonModOldVarsEquality = SmtUtils.and(mManagedScript.getScript(),
					oldVarEqualities.toArray(new Term[oldVarEqualities.size()]));
			if (mUseNamedTerms) {
				final Annotation annot = new Annotation(ANNOT_NAMED, ID_PRECONDITION_NON_MOD_GLOBAL_EQUALITY);
				nonModOldVarsEquality = mManagedScript.annotate(this, nonModOldVarsEquality, annot);
			}
			quickCheck = mManagedScript.assertTerm(this, nonModOldVarsEquality);
		}
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}

	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs in vars that is not contained in
	 * oldVarsOfModifiableGlobals there is an equality (= c_g c_old(g)) where c_g is the default constant of the global
	 * variable g and c_old(g) is the default constant of old(g).
	 */
	protected static Collection<Term> constructNonModOldVarsEquality(final Set<IProgramVar> vars,
			final Set<IProgramNonOldVar> oldVarsOfModifiableGlobals, final ManagedScript mgdScript, final Object lock) {
		final Collection<Term> conjunction = new ArrayList<>();
		for (final IProgramVar bv : vars) {
			if (bv instanceof IProgramOldVar) {
				final IProgramNonOldVar pnov = ((IProgramOldVar) bv).getNonOldVar();
				if (!oldVarsOfModifiableGlobals.contains(pnov)) {
					conjunction.add(oldVarsEquality((IProgramOldVar) bv, mgdScript, lock));
				}
			}
		}
		return conjunction;
	}

	static private Term oldVarsEquality(final IProgramOldVar oldVar, final ManagedScript mgdScript, final Object lock) {
		assert oldVar.isOldvar();
		final IProgramVar nonOldVar = oldVar.getNonOldVar();
		final Term equality = mgdScript.term(lock, "=", oldVar.getDefaultConstant(), nonOldVar.getDefaultConstant());
		return equality;
	}

	private void unAssertPrecondition() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null : "No PrePred asserted";
		mAssertedPrecond = null;
		mManagedScript.pop(this, 1);

		if (mAssertedAction == null) {
			throw new AssertionError("CodeBlock is assigned first");
		}
	}

	protected LBool assertCodeBlock(final IAction act) {
		if (mManagedScript.isLocked()) {
			mManagedScript.requestLockRelease();
		}
		mManagedScript.lock(this);
		mManagedScript.echo(this, new QuotedObject(MSG_START_EDGE_CHECK));
		assert mAssertedAction == null : "CodeBlock already asserted";
		mAssertedAction = act;

		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);

		Term cbFormula;
		if (act instanceof IInternalAction) {
			cbFormula = ((IInternalAction) act).getTransformula().getClosedFormula();
		} else if (act instanceof ICallAction) {
			cbFormula = ((ICallAction) act).getLocalVarsAssignment().getClosedFormula();
		} else if (act instanceof IReturnAction) {
			cbFormula = ((IReturnAction) act).getAssignmentOfReturn().getClosedFormula();
		} else {
			throw new AssertionError("unknown action");
		}
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_TRANSITION_FORMULA);
			cbFormula = mManagedScript.annotate(this, cbFormula, annot);
		}
		LBool quickCheck = mManagedScript.assertTerm(this, cbFormula);
		if (act instanceof IReturnAction) {
			mHierConstants = new ScopedHashMap<>();
			final IReturnAction ret = (IReturnAction) act;
			final String proc = ret.getPrecedingProcedure();
			final UnmodifiableTransFormula ovaTF = mOldVarsAssignmentCache.getOldVarsAssignment(proc);
			Term ovaFormula = ovaTF.getFormula();

			// rename modifiable globals to Hier vars
			ovaFormula = renameVarsToHierConstants(ovaTF.getInVars(), ovaFormula);
			// rename oldVars of modifiable globals to default vars
			ovaFormula = renameVarsToDefaultConstants(ovaTF.getOutVars(), ovaFormula);
			if (UNLET_TERMS) {
				ovaFormula = (new FormulaUnLet()).unlet(ovaFormula);
			}
			assert ovaFormula.getFreeVars().length == 0;
			if (mUseNamedTerms) {
				final Annotation annot = new Annotation(ANNOT_NAMED, ID_TRANSITION_MODIFIABLE_GLOBAL_EQUALITY);
				ovaFormula = mManagedScript.annotate(this, ovaFormula, annot);
			}
			quickCheck = mManagedScript.assertTerm(this, ovaFormula);

			final Set<IProgramVar> modifiableGlobals = ovaTF.getInVars().keySet();
			final UnmodifiableTransFormula callTf = ret.getLocalVarsAssignmentOfCall();
			Term locVarAssign = callTf.getFormula();
			// TODO: rename non-modifiable globals to DefaultConstants
			locVarAssign =
					renameNonModifiableGlobalsToDefaultConstants(callTf.getInVars(), modifiableGlobals, locVarAssign);

			// rename arguments vars to Hier vars
			locVarAssign = renameVarsToHierConstants(callTf.getInVars(), locVarAssign);
			// rename proc parameter vars to DefaultConstants
			locVarAssign = renameVarsToDefaultConstants(callTf.getOutVars(), locVarAssign);
			// rename auxiliary vars to fresh constants
			locVarAssign = renameAuxVarsToCorrespondingConstants(callTf.getAuxVars(), locVarAssign);
			if (UNLET_TERMS) {
				locVarAssign = (new FormulaUnLet()).unlet(locVarAssign);
			}
			assert locVarAssign.getFreeVars().length == 0;
			if (mUseNamedTerms) {
				final Annotation annot = new Annotation(ANNOT_NAMED, ID_LOCAL_VARS_ASSIGNMENT);
				locVarAssign = mManagedScript.annotate(this, locVarAssign, annot);
			}
			quickCheck = mManagedScript.assertTerm(this, locVarAssign);
		}
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}

	protected void unAssertCodeBlock() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedAction != null : "No CodeBlock asserted";
		mAssertedAction = null;
		mHierConstants = null;
		mManagedScript.pop(this, 1);
		if (mAssertedPrecond == null) {
			mManagedScript.echo(this, new QuotedObject(MSG_END_EDGE_CHECK));
			mManagedScript.unlock(this);
		} else {
			throw new AssertionError("CodeBlock is unasserted last");
		}
	}

	protected LBool assertHierPred(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedAction != null : "assert Return first";
		assert mAssertedAction instanceof IReturnAction : "assert Return first";
		assert mAssertedPrecond != null : "assert precond fist";
		assert mAssertedHier == null : "HierPred already asserted";
		mAssertedHier = p;
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mHierConstants.beginScope();
		Term hierFormula = p.getFormula();

		// rename globals that are not modifiable by callee to default constants
		final String callee = mAssertedAction.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCallee =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(callee);
		hierFormula =
				renameNonModifiableNonOldGlobalsToDefaultConstants(p.getVars(), modifiableGlobalsCallee, hierFormula);

		// rename oldvars of globals that are not modifiable by caller to
		// default constants of nonOldVar
		final String caller = mAssertedAction.getSucceedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCaller =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(caller);
		hierFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(), modifiableGlobalsCaller,
				hierFormula, mManagedScript, this);

		// rename vars which are assigned on return to Hier vars
		hierFormula = renameVarsToHierConstants(p.getVars(), hierFormula);
		if (UNLET_TERMS) {
			hierFormula = (new FormulaUnLet()).unlet(hierFormula);
		}

		// TODO auxvars
		assert hierFormula.getFreeVars().length == 0;

		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_HIERACHICAL_PRECONDITION);
			hierFormula = mManagedScript.annotate(this, hierFormula, annot);
		}
		final LBool quickCheck = mManagedScript.assertTerm(this, hierFormula);

		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}

	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs in vars and for which the corresponding
	 * nonOldVar occurs in modifiableGlobalsCaller but not in modifiableGlobalsCallee we add the equality (= c_old(g)
	 * c_g_hier) and for each nonOldVar that occurs in modifiableGlobalsCaller but not in modifiableGlobalsCallee we add
	 * the equality (= c_g c_g_hier), where c_g is the default constant of the global variable g and c_old(g) is the
	 * default constant of old(g) and c_g_hier is the constant for the nonOldVar g at the position of the hierarchical
	 * predecessor.
	 */
	private Collection<Term> constructCalleeNonModOldVarsEquality(final Set<IProgramVar> vars,
			final Set<IProgramVar> modifiableGlobalsCaller, final Set<IProgramVar> modifiableGlobalsCallee) {
		if (!modifiableGlobalsCallee.containsAll(modifiableGlobalsCaller)) {
			final boolean test = true;
		}
		final Collection<Term> conjunction = new ArrayList<>();
		for (final IProgramVar bv : vars) {
			if (bv instanceof GlobalBoogieVar) {
				IProgramNonOldVar bnov;
				if (bv instanceof IProgramOldVar) {
					bnov = ((IProgramOldVar) bv).getNonOldVar();
				} else {
					bnov = (IProgramNonOldVar) bv;
				}
				if (modifiableGlobalsCaller.contains(bnov) && !modifiableGlobalsCallee.contains(bnov)) {
					final Term hierConst = getOrConstructHierConstant(bnov);
					final Term conjunct =
							SmtUtils.binaryEquality(mManagedScript.getScript(), bv.getDefaultConstant(), hierConst);
					conjunction.add(conjunct);
				}
			}
		}
		return conjunction;
	}

	protected void unAssertHierPred() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedHier != null : "No HierPred asserted";
		assert mAssertedAction instanceof IReturnAction : MSG_WRONG_KIND_OF_ACTION;
		mAssertedHier = null;
		mManagedScript.pop(this, 1);
		mHierConstants.endScope();
	}

	private LBool assertPostcondInternal(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null;
		assert mAssertedAction != null;
		assert mAssertedAction instanceof IInternalAction : MSG_WRONG_KIND_OF_ACTION;
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mAssertedPostcond = p;

		// OldVars renamed (depending on modifiability)
		// All variables get index 0
		// assigned vars (locals and globals) get index 1
		// other vars get index 0
		Term renamedFormula = constructPostcondFormula(p, (IInternalAction) mAssertedAction,
				mModifiableGlobalVariableManager, mManagedScript, this);
		if (UNLET_TERMS) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = mManagedScript.term(this, "not", renamedFormula);
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_NEGATED_POSTCONDITION);
			negation = mManagedScript.annotate(this, negation, annot);
		}
		final LBool isSat = mManagedScript.assertTerm(this, negation);
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return isSat;
	}

	public static Term constructPostcondFormula(final IPredicate p, final IInternalAction action,
			final ModifiableGlobalsTable mgt, final ManagedScript mgdScript, final Object lock) {
		final Set<IProgramVar> assignedVars = action.getTransformula().getAssignedVars();
		Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula(), mgdScript, lock);
		final String succProc = action.getSucceedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mgt.getModifiedBoogieVars(succProc);
		renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(), modifiableGlobals,
				renamedFormula, mgdScript, lock);
		renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula, mgdScript, lock);
		return renamedFormula;
	}

	private LBool assertPostcondCall(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null;
		assert mAssertedAction != null;
		assert mAssertedAction instanceof ICallAction : MSG_WRONG_KIND_OF_ACTION;
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mAssertedPostcond = p;

		final Set<IProgramVar> boogieVars = p.getVars();
		// rename oldVars to default constants of non-oldvars
		Term renamedFormula = renameGlobalsAndOldVarsToNonOldDefaultConstants(boogieVars, p.getFormula());
		// rename remaining variables
		renamedFormula = renameVarsToPrimedConstants(boogieVars, renamedFormula, mManagedScript, this);
		renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula, mManagedScript, this);
		if (UNLET_TERMS) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = mManagedScript.term(this, "not", renamedFormula);
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_NEGATED_POSTCONDITION);
			negation = mManagedScript.annotate(this, negation, annot);
		}
		final LBool isSat = mManagedScript.assertTerm(this, negation);
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return isSat;
	}

	private LBool assertPostcondReturn(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null;
		assert mAssertedAction instanceof IReturnAction : MSG_WRONG_KIND_OF_ACTION;
		assert mAssertedHier != null;
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mHierConstants.beginScope();
		mAssertedPostcond = p;

		// rename assignedVars to primed vars
		final Set<IProgramVar> assignedVars =
				((IReturnAction) mAssertedAction).getAssignmentOfReturn().getAssignedVars();
		Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula(), mManagedScript, this);

		final String callee = mAssertedAction.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCallee =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(callee);

		// rename modifiable globals to default constants
		renamedFormula = renameVarsToDefaultConstants(modifiableGlobalsCallee, renamedFormula, mManagedScript, this);

		// rename globals that are not modifiable by callee to default constants
		renamedFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(p.getVars(), modifiableGlobalsCallee,
				renamedFormula);

		// rename oldvars of globals that are not modifiable by caller to
		// default constants of nonOldVar
		final String caller = mAssertedAction.getSucceedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCaller =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(caller);
		renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(), modifiableGlobalsCaller,
				renamedFormula, mManagedScript, this);

		// rename remaining non-old Globals to default constants
		// renamedFormula = renameNonOldGlobalsToDefaultConstants(p.getVars(), renamedFormula);

		// rename remaining vars to Hier vars
		renamedFormula = renameVarsToHierConstants(p.getVars(), renamedFormula);

		if (UNLET_TERMS) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = mManagedScript.term(this, "not", renamedFormula);

		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_NEGATED_POSTCONDITION);
			negation = mManagedScript.annotate(this, negation, annot);
		}
		final LBool isSat = mManagedScript.assertTerm(this, negation);
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return isSat;
	}

	protected void unAssertPostcondition() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedAction != null : "Assert CodeBlock first!";
		assert mAssertedPrecond != null : "Assert precond first!";
		assert mAssertedPostcond != null : "Assert postcond first!";
		mAssertedPostcond = null;
		mCounterexampleStatePrecond = null;
		mCounterexampleStatePostcond = null;
		mManagedScript.pop(this, 1);
		if (mAssertedAction instanceof IReturnAction) {
			assert mHierConstants != null : "Assert hierPred first!";
			assert mAssertedHier != null : "Assert hierPred first!";
			mHierConstants.endScope();
		}
	}

	protected Validity checkValidity() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedAction != null : "Assert CodeBlock first!";
		assert mAssertedPrecond != null : "Assert precond first! ";
		assert mAssertedPostcond != null : "Assert postcond first! ";
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		final LBool isSat = mManagedScript.checkSat(this);
		switch (isSat) {
		case SAT:
			if (mConstructCounterexamples) {
				mCounterexampleStatePrecond = constructCounterexampleStateForPrecondition();
				mCounterexampleStatePostcond = constructCounterexampleStateForPostcondition();
			}
			mEdgeCheckerBenchmark.getSolverCounterSat().incRe();
			break;
		case UNKNOWN:
			mEdgeCheckerBenchmark.getSolverCounterUnknown().incRe();
			break;
		case UNSAT:
			mEdgeCheckerBenchmark.getSolverCounterUnsat().incRe();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return IHoareTripleChecker.convertLBool2Validity(isSat);
	}

	private ProgramState<Term> constructCounterexampleStateForPrecondition() {
		final UnmodifiableTransFormula tf = mAssertedAction.getTransformula();
		return constructCounterexampleState(tf.getInVars(), TransFormulaUtils::constructOutvarsToInvarsMap,
				x -> TransFormulaUtils.renameInvarsToDefaultVars(tf, mManagedScript, x));
	}


	private ProgramState<Term> constructCounterexampleStateForPostcondition() {
		final UnmodifiableTransFormula tf = mAssertedAction.getTransformula();
		return constructCounterexampleState(tf.getOutVars(), TransFormulaUtils::constructInvarsToOutvarsMap,
				x -> TransFormulaUtils.renameOutvarsToDefaultVars(tf, mManagedScript, x));
	}

	private ProgramState<Term> constructCounterexampleState(final Map<IProgramVar, TermVariable> xVars,
			final Function<TransFormula, Map<TermVariable, TermVariable>> toXVarsMap,
			final Function<Term, Term> xVarToDefaultVar) {
		final Map<Term, Term> representativeTerm2ClosedTerm = new HashMap<>();
		final UnmodifiableTransFormula tf = mAssertedAction.getTransformula();
		for (final Entry<IProgramVar, TermVariable> entry : xVars.entrySet()) {
			if (SmtUtils.isSortForWhichWeCanGetValues(entry.getKey().getTermVariable().getSort())) {
				final Term xVarConst = UnmodifiableTransFormula.computeClosedFormula(xVars.get(entry.getKey()),
						tf.getInVars(), tf.getOutVars(), Collections.emptySet(), mManagedScript);
				representativeTerm2ClosedTerm.put(entry.getKey().getTermVariable(), xVarConst);
			}
		}
		final Set<TermVariable> inAndOutVars = tf.getInVars().entrySet().stream().map(x -> x.getValue())
				.collect(Collectors.toSet());
		inAndOutVars.addAll(tf.getOutVars().entrySet().stream().map(x -> x.getValue()).collect(Collectors.toSet()));
		final Set<Term> selectTerms = new SubTermFinder(x -> isSuitableArrayReadTerm(x, inAndOutVars))
				.findMatchingSubterms(tf.getFormula());
		for (final Term selectTerm : selectTerms) {
			final Term selectTermAllOut = new Substitution(mManagedScript,
					toXVarsMap.apply(tf)).transform(selectTerm);
			final Term selectTermWithDefaultVars = xVarToDefaultVar.apply(selectTermAllOut);
			// version of the select term as is was asserted
			final Term selectTermClosed = UnmodifiableTransFormula.computeClosedFormula(selectTermAllOut,
					tf.getInVars(), tf.getOutVars(), Collections.emptySet(), mManagedScript);
			representativeTerm2ClosedTerm.put(selectTermWithDefaultVars, selectTermClosed);
		}
		return generateProgramState(representativeTerm2ClosedTerm);
	}

	private ProgramState<Term> generateProgramState(final Map<Term, Term> representativeTerm2ClosedTerm) {
		final Map<Term, Collection<Term>> valuesMapping = new HashMap<>();
		for (final Entry<Term, Term> entry : representativeTerm2ClosedTerm.entrySet()) {
			final Map<Term, Term> values = mManagedScript.getValue(this, new Term[] { entry.getValue() });
			final Term value = values.get(entry.getValue());
			valuesMapping.put(entry.getKey(), Collections.singletonList(value));
		}
		return new ProgramState<>(valuesMapping, Term.class);
	}

	/**
	 * @param varSet here, these are inVar or outVars of a TransFormula
	 * @return true iff term is an array select term, whose Sort allows us to get values and whose
	 * free variables are in the set varSet.
	 */
	private boolean isSuitableArrayReadTerm(final Term term, final Set<TermVariable> varSet) {
		return (term instanceof ApplicationTerm)
				&& ((ApplicationTerm) term).getFunction().getName().equals("select")
				&& SmtUtils.isSortForWhichWeCanGetValues(term.getSort())
				&& Arrays.stream(term.getFreeVars()).allMatch(x -> varSet.contains(x));
	}

	private static Term renameVarsToDefaultConstants(final Set<? extends IProgramVar> set, final Term formula,
			final ManagedScript managedScript, final Object lock) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final IProgramVar bv : set) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getDefaultConstant());
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return managedScript.let(lock, vars, values, formula);
	}

	private Term renameVarsToDefaultConstants(final Map<IProgramVar, TermVariable> bv2tv, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();

		for (final Entry<IProgramVar, TermVariable> bv : bv2tv.entrySet()) {
			replacees.add(bv.getValue());
			replacers.add(bv.getKey().getDefaultConstant());
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	private static Term renameVarsToPrimedConstants(final Set<IProgramVar> boogieVars, final Term formula,
			final ManagedScript managedScript, final Object lock) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final IProgramVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getPrimedConstant());
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return managedScript.let(lock, vars, values, formula);
	}

	private Term renameVarsToHierConstants(final Set<IProgramVar> boogieVars, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final IProgramVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(getOrConstructHierConstant(bv));
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	private Term renameVarsToHierConstants(final Map<IProgramVar, TermVariable> bv2tv, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final Entry<IProgramVar, TermVariable> entry : bv2tv.entrySet()) {
			replacees.add(entry.getValue());
			replacers.add(getOrConstructHierConstant(entry.getKey()));
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	private Term renameAuxVarsToCorrespondingConstants(final Set<TermVariable> auxVars, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final TermVariable auxVarTv : auxVars) {
			replacees.add(auxVarTv);
			final Term correspondingConstant =
					mManagedScript.term(this, ProgramVarUtils.generateConstantIdentifierForAuxVar(auxVarTv));
			replacers.add(correspondingConstant);
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	private Term getOrConstructHierConstant(final IProgramVar bv) {
		Term preHierConstant = mHierConstants.get(bv);
		if (preHierConstant == null) {
			final String name = "c_" + bv.getTermVariable().getName() + "_Hier";
			final Sort sort = bv.getTermVariable().getSort();
			mManagedScript.declareFun(this, name, new Sort[0], sort);
			preHierConstant = mManagedScript.term(this, name);
			mHierConstants.put(bv, preHierConstant);
		}
		return preHierConstant;
	}

	/**
	 * Rename each g in boogieVars that is not contained in modifiableGlobals to c_g, where c_g is the default constant
	 * for g.
	 */
	private Term renameNonModifiableNonOldGlobalsToDefaultConstants(final Set<IProgramVar> boogieVars,
			final Set<IProgramNonOldVar> modifiableGlobalsCallee, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final IProgramVar bv : boogieVars) {
			if (bv.isGlobal() && bv instanceof IProgramNonOldVar && !modifiableGlobalsCallee.contains(bv)) {
				replacees.add(bv.getTermVariable());
				replacers.add(bv.getDefaultConstant());
			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	/**
	 * Rename oldVars old(g) of non-modifiable globals to the default constants of g.
	 */
	private static Term renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(final Set<IProgramVar> boogieVars,
			final Set<IProgramNonOldVar> modifiableGlobalsCaller, final Term formula, final ManagedScript mgdScript,
			final Object lock) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final IProgramVar bv : boogieVars) {
			if (bv instanceof IProgramOldVar) {
				final IProgramNonOldVar nonOldVar = ((IProgramOldVar) bv).getNonOldVar();
				if (modifiableGlobalsCaller.contains(nonOldVar)) {
					// do nothing
				} else {
					replacees.add(bv.getTermVariable());
					replacers.add(nonOldVar.getDefaultConstant());
				}

			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mgdScript.let(lock, vars, values, formula);
	}

	private Term renameNonModifiableGlobalsToDefaultConstants(final Map<IProgramVar, TermVariable> boogieVars,
			final Set<IProgramVar> modifiableGlobals, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final Entry<IProgramVar, TermVariable> entry : boogieVars.entrySet()) {
			final IProgramVar bv = entry.getKey();
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					assert !modifiableGlobals.contains(bv);
					// do nothing
				} else {
					if (modifiableGlobals.contains(bv)) {
						// do noting
					} else {
						// oldVar of global which is not modifiable by called proc
						replacees.add(entry.getValue());
						replacers.add(bv.getDefaultConstant());
					}
				}
			} else {
				assert !modifiableGlobals.contains(bv);
			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	private Term renameGlobalsAndOldVarsToNonOldDefaultConstants(final Set<IProgramVar> boogieVars,
			final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();
		for (final IProgramVar bv : boogieVars) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					replacees.add(bv.getTermVariable());
					final IProgramVar nonOldbv = ((IProgramOldVar) bv).getNonOldVar();
					replacers.add(nonOldbv.getDefaultConstant());
				} else {
					replacees.add(bv.getTermVariable());
					replacers.add(bv.getDefaultConstant());
				}
			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars, values, formula);
	}

	public boolean isAssertionStackEmpty() {
		if (mAssertedAction == null) {
			assert mAssertedPrecond == null;
			assert mAssertedHier == null;
			return true;
		}
		return false;
	}

	public ProgramState<Term> getCounterexampleStatePrecond() {
		if (!mConstructCounterexamples) {
			throw new IllegalStateException("Construction of counterexamples is not enabled.");
		}
		if (mCounterexampleStatePrecond == null) {
			throw new IllegalStateException("Last response was valid or assertion stack has been altered.");
		}
		return mCounterexampleStatePrecond;
	}

	public ProgramState<Term> getCounterexampleStatePostcond() {
		if (!mConstructCounterexamples) {
			throw new IllegalStateException("Construction of counterexamples is not enabled.");
		}
		if (mCounterexampleStatePrecond == null) {
			throw new IllegalStateException("Last response was valid or assertion stack has been altered.");
		}
		return mCounterexampleStatePostcond;
	}
}
