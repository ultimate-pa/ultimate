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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.GlobalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript.ILockHolderWithVoluntaryLockRelease;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class IncrementalHoareTripleChecker implements IHoareTripleChecker, ILockHolderWithVoluntaryLockRelease  {
	
	protected final ManagedScript mManagedScript;
	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;
	
	private IPredicate mAssertedPrecond;
	private IPredicate mAssertedHier;
	private IAction mAssertedAction;
	private IPredicate mAssertedPostcond;
	private ScopedHashMap<IProgramVar, Term> mHierConstants;
	public final boolean mUseNamedTerms = true;
	public final static boolean mUnletTerms = true;
	
	protected static final String s_IdPrecondition = "precondition";
	protected static final String s_PrecondNonModGlobalEquality = "precondNonModGlobalEquality";
	protected static final String s_IdTransitionModifiableGlobalEquality = "modifiableVarEquality";
	protected static final String s_IdTransitionFormula = "codeBlock";
	protected static final String s_IdLocalVarsAssignment = "localVarsAssignment";
	protected static final String s_IdHierarchicalPrecondition = "hierarchicalPrecondition";
	protected static final String s_IdNegatedPostcondition = "negatedPostcondition";
	
	private final HoareTripleCheckerStatisticsGenerator mEdgeCheckerBenchmark;
	
	
	private static final String s_StartEdgeCheck = "starting to check validity of Hoare triples";
	private static final String s_EndEdgeCheck = "finished to check validity of Hoare triples";
	
	public IncrementalHoareTripleChecker(final ManagedScript managedScript, 
			final ModifiableGlobalVariableManager modGlobVarManager) {
		mManagedScript = managedScript;
		mModifiableGlobalVariableManager = modGlobVarManager;
		mEdgeCheckerBenchmark = new HoareTripleCheckerStatisticsGenerator();
	}
	
	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mEdgeCheckerBenchmark;
	}
	
	
	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		final LBool quickCheck_Trans = prepareAssertionStackAndAddTransition(act);
		if (quickCheck_Trans == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_LinPred = prepareAssertionStackAndAddPrecondition(pre);
		if (quickCheck_LinPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_Postcond = prepareAssertionStackAndAddPostcond(post);
		if (quickCheck_Postcond == LBool.UNSAT) {
			return Validity.VALID;
		}
		assert quickCheck_Postcond == LBool.UNKNOWN || quickCheck_Postcond == null : "unexpected quickcheck result";
		assert mAssertedPrecond == pre && mAssertedHier == null && 
				mAssertedAction == act && mAssertedPostcond == post;
		return checkValidity();
	}
	
	
	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
		final LBool quickCheck_Trans = prepareAssertionStackAndAddTransition(act);
		if (quickCheck_Trans == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_LinPred = prepareAssertionStackAndAddPrecondition(pre);
		if (quickCheck_LinPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_Postcond = prepareAssertionStackAndAddPostcond(post);
		if (quickCheck_Postcond == LBool.UNSAT) {
			return Validity.VALID;
		}
		assert quickCheck_Postcond == LBool.UNKNOWN || quickCheck_Postcond == null : "unexpected quickcheck result";
		assert mAssertedPrecond == pre && mAssertedHier == null && 
				mAssertedAction == act && mAssertedPostcond == post;
		return checkValidity();
	}

	
	@Override
	public Validity checkReturn(final IPredicate linPre, final IPredicate hierPre,
			final IReturnAction act, final IPredicate postcond) {
		final LBool quickCheck_Trans = prepareAssertionStackAndAddTransition(act);
		if (quickCheck_Trans == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_LinPred = prepareAssertionStackAndAddPrecondition(linPre);
		if (quickCheck_LinPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_HierPred = prepareAssertionStackAndAddHierpred(hierPre);
		if (quickCheck_HierPred == LBool.UNSAT) {
			return Validity.VALID;
		}
		final LBool quickCheck_Postcond = prepareAssertionStackAndAddPostcond(postcond);
		if (quickCheck_Postcond == LBool.UNSAT) {
			return Validity.VALID;
		}
		assert quickCheck_Postcond == LBool.UNKNOWN || quickCheck_Postcond == null : "unexpected quickcheck result";
		assert mAssertedPrecond == linPre && mAssertedHier == hierPre && 
				mAssertedAction == act && mAssertedPostcond == postcond;
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
			return assertPostcond_Internal(postcond);
		} else if (mAssertedAction instanceof ICallAction) {
			return assertPostcond_Call(postcond);
		} else if (mAssertedAction instanceof IReturnAction) {
			return assertPostcond_Return(postcond);
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
		if (mAssertedAction instanceof IReturnAction) {
			mHierConstants.beginScope();
		}
		Term predcondition = p.getClosedFormula();
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(":named", s_IdPrecondition);
			predcondition = mManagedScript.annotate(this, predcondition, annot);
		}
		LBool quickCheck = mManagedScript.assertTerm(this, predcondition);
		final String predProc = mAssertedAction.getPreceedingProcedure();
		final Set<IProgramVar> oldVarsOfModifiable = mModifiableGlobalVariableManager.
				getOldVarsAssignment(predProc).getAssignedVars();
		final Collection<Term> oldVarEqualities = constructNonModOldVarsEquality(p.getVars(), oldVarsOfModifiable);
		if (!oldVarEqualities.isEmpty()) {
			Term nonModOldVarsEquality = Util.and(mManagedScript.getScript(), oldVarEqualities.toArray(new Term[oldVarEqualities.size()]));
			if (mUseNamedTerms) {
				final Annotation annot = new Annotation(":named", s_PrecondNonModGlobalEquality);
				nonModOldVarsEquality = mManagedScript.annotate(this, nonModOldVarsEquality, annot);
			}
			quickCheck = mManagedScript.assertTerm(this, nonModOldVarsEquality);
		}
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}
	
	
	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs
	 * in vars that is not contained in oldVarsOfModifiableGlobals there is
	 * an equality (= c_g c_old(g)) where c_g is the default constant of the 
	 * global variable g and c_old(g) is the default constant of old(g).
	 */
	private Collection<Term> constructNonModOldVarsEquality(final Set<IProgramVar> vars,
			final Set<IProgramVar> oldVarsOfModifiableGlobals) {
		final Collection<Term> conjunction = new ArrayList<>();
		for (final IProgramVar bv : vars) {
			if (bv instanceof IProgramOldVar && !oldVarsOfModifiableGlobals.contains(bv)) {
				conjunction.add(oldVarsEquality((IProgramOldVar) bv));
			}
		}
		return conjunction;
	}
	
	private Term oldVarsEquality(final IProgramOldVar oldVar) {
		assert oldVar.isOldvar();
		final IProgramVar nonOldVar = oldVar.getNonOldVar();
		final Term equality = mManagedScript.term(this, "=", oldVar.getDefaultConstant(), 
										   nonOldVar.getDefaultConstant());
		return equality;
	}
	

	private void unAssertPrecondition() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null : "No PrePred asserted";
		mAssertedPrecond = null;
		mManagedScript.pop(this, 1);
		if (mAssertedAction instanceof IReturnAction) {
			mHierConstants.endScope();
		}
		if (mAssertedAction == null) {
			throw new AssertionError("CodeBlock is assigned first");
		}
	}
	
	
	protected LBool assertCodeBlock(final IAction act) {
		if (mManagedScript.isLocked()) {
			mManagedScript.requestLockRelease();
		}
		mManagedScript.lock(this);
		mManagedScript.echo(this, new QuotedObject(s_StartEdgeCheck));
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
			final Annotation annot = new Annotation(":named", s_IdTransitionFormula);
			cbFormula = mManagedScript.annotate(this, cbFormula, annot);
		}
		LBool quickCheck = mManagedScript.assertTerm(this, cbFormula);
		if (act instanceof IReturnAction) {
			mHierConstants = new ScopedHashMap<IProgramVar,Term>();
			final IReturnAction ret = (IReturnAction) act;
			final String proc = ret.getPreceedingProcedure();
			final UnmodifiableTransFormula ovaTF = mModifiableGlobalVariableManager.
					getOldVarsAssignment(proc);
			Term ovaFormula = ovaTF.getFormula();

			//rename modifiable globals to Hier vars
			ovaFormula = renameVarsToHierConstants(ovaTF.getInVars(), ovaFormula);
			//rename oldVars of modifiable globals to default vars
			ovaFormula = renameVarsToDefaultConstants(ovaTF.getOutVars(), ovaFormula);
			if (mUnletTerms ) {
				ovaFormula = (new FormulaUnLet()).unlet(ovaFormula);
			}
			assert ovaFormula.getFreeVars().length == 0;
			if (mUseNamedTerms) {
				final Annotation annot = new Annotation(":named", s_IdTransitionModifiableGlobalEquality);
				ovaFormula = mManagedScript.annotate(this, ovaFormula, annot);
			}
			quickCheck = mManagedScript.assertTerm(this, ovaFormula);
			
			final Set<IProgramVar> modifiableGlobals = ovaTF.getInVars().keySet();
			final UnmodifiableTransFormula callTf = ret.getLocalVarsAssignmentOfCall();
			Term locVarAssign = callTf.getFormula();
			//TODO: rename non-modifiable globals to DefaultConstants
			locVarAssign = renameNonModifiableGlobalsToDefaultConstants(
					callTf.getInVars(), modifiableGlobals, locVarAssign);
			
			//rename arguments vars to Hier vars
			locVarAssign = renameVarsToHierConstants(callTf.getInVars(), locVarAssign);
			//rename proc parameter vars to DefaultConstants
			locVarAssign = renameVarsToDefaultConstants(callTf.getOutVars(), locVarAssign);
			//rename auxiliary vars to fresh constants
			locVarAssign = renameAuxVarsToCorrespondingConstants(callTf.getAuxVars(), locVarAssign);
			if (mUnletTerms ) {
				locVarAssign = (new FormulaUnLet()).unlet(locVarAssign);
			}
			assert locVarAssign.getFreeVars().length == 0;
			if (mUseNamedTerms) {
				final Annotation annot = new Annotation(":named", s_IdLocalVarsAssignment);
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
			mManagedScript.echo(this, new QuotedObject(s_EndEdgeCheck));
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
		final String callee = mAssertedAction.getPreceedingProcedure();
		final Set<IProgramVar> modifiableGlobalsCallee = mModifiableGlobalVariableManager.
				getModifiedBoogieVars(callee);
		hierFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(
				p.getVars(), modifiableGlobalsCallee, hierFormula);
		
		// rename oldvars of globals that are not modifiable by caller to 
		// default constants of nonOldVar
		final String caller = mAssertedAction.getSucceedingProcedure();
		final Set<IProgramVar> modifiableGlobalsCaller = mModifiableGlobalVariableManager.
				getModifiedBoogieVars(caller);
		hierFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(
				p.getVars(), modifiableGlobalsCaller, hierFormula);
		
		//rename vars which are assigned on return to Hier vars
		hierFormula = renameVarsToHierConstants(p.getVars(), hierFormula);
		if (mUnletTerms ) {
			hierFormula = (new FormulaUnLet()).unlet(hierFormula);
		}
		
		//TODO auxvars
		assert hierFormula.getFreeVars().length == 0;
		
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(":named", s_IdHierarchicalPrecondition);
			hierFormula = mManagedScript.annotate(this, hierFormula, annot);
		}
		final LBool quickCheck = mManagedScript.assertTerm(this, hierFormula);
		
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}
	

	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs
	 * in vars and for which the corresponding nonOldVar occurs in 
	 * modifiableGlobalsCaller but not in modifiableGlobalsCallee we add the
	 * equality (= c_old(g) c_g_hier) and
	 * for each nonOldVar that occurs in 
	 * modifiableGlobalsCaller but not in modifiableGlobalsCallee we add the
	 * equality (= c_g c_g_hier),
	 * where c_g is the default constant of the 
	 * global variable g and c_old(g) is the default constant of old(g) and
	 * c_g_hier is the constant for the nonOldVar g at the position of the
	 * hierarchical predecessor.
	 */
	private Collection<Term> constructCalleeNonModOldVarsEquality(final Set<IProgramVar> vars,
			final Set<IProgramVar> modifiableGlobalsCaller,
			final Set<IProgramVar> modifiableGlobalsCallee) {
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
				if (modifiableGlobalsCaller.contains(bnov) && 
						!modifiableGlobalsCallee.contains(bnov)) {
					final Term hierConst = getOrConstructHierConstant(bnov);
					final Term conjunct = SmtUtils.binaryEquality(mManagedScript.getScript(), bv.getDefaultConstant(), hierConst);
					conjunction.add(conjunct);
				}
			}
		}
		return conjunction;
	}

	
	private void unAssertHierPred() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedHier != null : "No HierPred asserted";
		assert (mAssertedAction instanceof IReturnAction) : "Wrong kind of action";
		mAssertedHier = null;
		mManagedScript.pop(this, 1);
		mHierConstants.endScope();
	}
	
	
	private LBool assertPostcond_Internal(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null;
		assert mAssertedAction != null;
		assert (mAssertedAction instanceof IInternalAction) : "Wrong kind of action";
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mAssertedPostcond = p;
		
		//OldVars renamed (depending on modifiability)
		//All variables get index 0 
		//assigned vars (locals and globals) get index 1
		//other vars get index 0
		final Set<IProgramVar> assignedVars = ((IInternalAction) mAssertedAction).getTransformula().getAssignedVars();
		Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula());
		final String succProc = mAssertedAction.getSucceedingProcedure();
		final Set<IProgramVar> modifiableGlobals = mModifiableGlobalVariableManager.getModifiedBoogieVars(succProc);
		renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(), modifiableGlobals, renamedFormula);
		renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula);
		if (mUnletTerms ) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = mManagedScript.term(this, "not", renamedFormula);
		if (mUseNamedTerms) {
			final Annotation annot = new Annotation(":named", s_IdNegatedPostcondition);
			negation = mManagedScript.annotate(this, negation, annot);
		}
		final LBool isSat = mManagedScript.assertTerm(this, negation);
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return isSat;
	}
	

	private LBool assertPostcond_Call(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null;
		assert mAssertedAction != null;
		assert (mAssertedAction instanceof ICallAction) : "Wrong kind of action";
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mAssertedPostcond = p;
		
		final Set<IProgramVar> boogieVars = p.getVars();
		// rename oldVars to default constants of non-oldvars
		Term renamedFormula = renameGlobalsAndOldVarsToNonOldDefaultConstants(
												boogieVars, p.getFormula());
		// rename remaining variables
		renamedFormula = renameVarsToPrimedConstants(boogieVars, renamedFormula);
		renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula);
		if (mUnletTerms ) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = mManagedScript.term(this, "not", renamedFormula);
		if (mUseNamedTerms) {
			final String name = "negatedPostcondition";
			final Annotation annot = new Annotation(":named", name);
			negation = mManagedScript.annotate(this, negation, annot);
		}
		final LBool isSat = mManagedScript.assertTerm(this, negation);
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return isSat;
	}



	private LBool assertPostcond_Return(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedPrecond != null;
		assert (mAssertedAction instanceof IReturnAction) : "Wrong kind of action";
		assert mAssertedHier != null;
		mEdgeCheckerBenchmark.continueEdgeCheckerTime();
		mManagedScript.push(this, 1);
		mHierConstants.beginScope();
		mAssertedPostcond = p;
		
		//rename assignedVars to primed vars
		final Set<IProgramVar> assignedVars = ((IReturnAction) mAssertedAction).getAssignmentOfReturn().getAssignedVars();
		Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula());
		
		final String callee = mAssertedAction.getPreceedingProcedure();
		final Set<IProgramVar> modifiableGlobalsCallee = mModifiableGlobalVariableManager.
				getModifiedBoogieVars(callee);
		
		//rename modifiable globals to default constants
		renamedFormula = renameVarsToDefaultConstants(modifiableGlobalsCallee, renamedFormula);
		
		// rename globals that are not modifiable by callee to default constants
		renamedFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(
				p.getVars(), modifiableGlobalsCallee, renamedFormula);
		
		// rename oldvars of globals that are not modifiable by caller to 
		// default constants of nonOldVar
		final String caller = mAssertedAction.getSucceedingProcedure();
		final Set<IProgramVar> modifiableGlobalsCaller = mModifiableGlobalVariableManager.
				getModifiedBoogieVars(caller);
		renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(
				p.getVars(), modifiableGlobalsCaller, renamedFormula);
		
		// rename remaining non-old Globals to default constants
//		renamedFormula = renameNonOldGlobalsToDefaultConstants(p.getVars(), renamedFormula);
		
		//rename remaining vars to Hier vars
		renamedFormula = renameVarsToHierConstants(p.getVars(), renamedFormula);
		
		if (mUnletTerms ) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = mManagedScript.term(this, "not", renamedFormula);

		if (mUseNamedTerms) {
			final String name = "negatedPostcondition";
			final Annotation annot = new Annotation(":named", name);
			negation = mManagedScript.annotate(this, negation, annot);
		}
		final LBool isSat = mManagedScript.assertTerm(this, negation);
		mEdgeCheckerBenchmark.stopEdgeCheckerTime();
		return isSat;
	}
	
	private void unAssertPostcondition() {
		assert mManagedScript.isLockOwner(this);
		assert mAssertedAction != null : "Assert CodeBlock first!";
		assert mAssertedPrecond != null : "Assert precond first!";
		assert mAssertedPostcond != null : "Assert postcond first!";
		mAssertedPostcond = null;
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
		return IHoareTripleChecker.lbool2validity(isSat);
	}
	

	
	

	
	
	private Term renameVarsToDefaultConstants(final Set<IProgramVar> boogieVars, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getDefaultConstant());
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}
	
	
	private Term renameVarsToDefaultConstants(final Map<IProgramVar, TermVariable> bv2tv, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : bv2tv.keySet()) {
			replacees.add(bv2tv.get(bv));
			replacers.add(bv.getDefaultConstant());
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}
	
	
	private Term renameVarsToPrimedConstants(final Set<IProgramVar> boogieVars, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getPrimedConstant());
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}


	private Term renameVarsToHierConstants(final Set<IProgramVar> boogieVars, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(getOrConstructHierConstant(bv));
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}
	
	private Term renameVarsToHierConstants(final Map<IProgramVar, TermVariable> bv2tv, final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : bv2tv.keySet()) {
			replacees.add(bv2tv.get(bv));
			replacers.add(getOrConstructHierConstant(bv));
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}
	
	private Term renameAuxVarsToCorrespondingConstants(final Set<TermVariable> auxVars,
			final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final TermVariable auxVarTv : auxVars) {
			replacees.add(auxVarTv);
			final Term correspondingConstant = 
					SmtUtils.termVariable2constant(mManagedScript.getScript(), auxVarTv, false);
			replacers.add(correspondingConstant);
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
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
	 * Rename each g in boogieVars that is not contained in modifiableGlobals
	 * to c_g, where c_g is the default constant for g.
	 */
	private Term renameNonModifiableNonOldGlobalsToDefaultConstants(
			final Set<IProgramVar> boogieVars, 
			final Set<IProgramVar> modifiableGlobals,
			final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : boogieVars) {
			if (bv.isGlobal()) {
				if (bv instanceof IProgramNonOldVar) {
					if (modifiableGlobals.contains(bv)) {
						//do nothing
					} else {
						replacees.add(bv.getTermVariable());
						replacers.add(bv.getDefaultConstant());
					}
				}
			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}
	
	
	/**
	 * Rename oldVars old(g) of non-modifiable globals to the
	 * default constants of g. 
	 */
	private Term renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(
			final Set<IProgramVar> boogieVars, 
			final Set<IProgramVar> modifiableGlobals,
			final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : boogieVars) {
			if (bv instanceof IProgramOldVar) {
				final IProgramNonOldVar nonOldVar = ((IProgramOldVar) bv).getNonOldVar();
				if (modifiableGlobals.contains(nonOldVar)) {
					//do nothing
				} else {
					replacees.add(bv.getTermVariable());
					replacers.add(nonOldVar.getDefaultConstant());
				}
				
			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}

	
	private Term renameNonModifiableGlobalsToDefaultConstants(
			final Map<IProgramVar,TermVariable> boogieVars, 
			final Set<IProgramVar> modifiableGlobals,
			final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
		for (final IProgramVar bv : boogieVars.keySet()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					assert !modifiableGlobals.contains(bv);
					// do nothing
				} else {
					if (modifiableGlobals.contains(bv)) {
						//do noting
					} else {
						//oldVar of global which is not modifiable by called proc
						replacees.add(boogieVars.get(bv));
						replacers.add(bv.getDefaultConstant());
					}
				}
			} else {
				assert !modifiableGlobals.contains(bv);
			}
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		return mManagedScript.let(this, vars , values, formula);
	}
	
	
	private Term renameGlobalsAndOldVarsToNonOldDefaultConstants(
			final Set<IProgramVar> boogieVars, 
			final Term formula) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();
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
		return mManagedScript.let(this, vars , values, formula);
	}
	
	
	public boolean isAssertionStackEmpty() {
		if (mAssertedAction == null) {
			assert mAssertedPrecond == null;
			assert mAssertedHier == null;
			return true;
		} else {
			return false;
		}
	}
	
}
