/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.OldVarsAssignmentCache;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * An {@link IHoareTripleChecker} that can be used to debug other {@link IHoareTripleChecker}s or things that generate
 * hoare triples (i.e., abstract interpretation).
 *
 * It tries to generate and print additional information (e.g., models or unsat cores) if a hoare triple check fails.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class DebuggingHoareTripleChecker implements IHoareTripleChecker {

	private static final String PREFIX = DebuggingHoareTripleChecker.class.getSimpleName() + "_";

	private static final String ANNOT_NAMED = ":named";
	private static final String ID_PRECONDITION = PREFIX + "precond";
	private static final String ID_PRECONDITION_NON_MOD_GLOBAL_EQUALITY = PREFIX + "precondNonModGlobalEquality";
	private static final String ID_TRANSITION_MODIFIABLE_GLOBAL_EQUALITY = PREFIX + "modifiableVarEquality";
	private static final String ID_LOCAL_VARS_ASSIGNMENT = PREFIX + "localVarsAssignment";
	private static final String ID_HIERACHICAL_PRECONDITION = PREFIX + "hierarchicalPrecondition";
	private static final String ID_NEGATED_POSTCONDITION = PREFIX + "notPostcond";
	private static final String MSG_START_EDGE_CHECK = PREFIX + "Start";
	private static final String MSG_END_EDGE_CHECK = PREFIX + "End";

	private static final boolean SIMPLIFY_IF_ASSERTION_FAILS = true;

	private final ManagedScript mManagedScript;
	private final ModifiableGlobalsTable mModifiableGlobalVariableManager;
	private final OldVarsAssignmentCache mOldVarsAssignmentCache;

	private ScopedHashMap<IProgramVar, Term> mHierConstants;

	private final Deque<Assertion> mAssertions;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private Validity mExpected;

	private boolean mIsLastOk;

	private final boolean mGenerateUnsatCore;

	public DebuggingHoareTripleChecker(final IUltimateServiceProvider services, final ILogger logger,
			final CfgSmtToolkit csToolkit, final Validity expected) {
		mLogger = logger;
		mServices = services;

		mManagedScript = csToolkit.getManagedScript();
		mModifiableGlobalVariableManager = csToolkit.getModifiableGlobalsTable();
		mOldVarsAssignmentCache = csToolkit.getOldVarsAssignmentCache();
		mAssertions = new ArrayDeque<>();
		mExpected = expected;
		final Object val = mManagedScript.getScript().getOption(":produce-unsat-cores");
		mGenerateUnsatCore = Boolean.parseBoolean(val.toString());
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		throw new UnsupportedOperationException(getClass().getName() + " does not support getEdgeCheckerBenchmark()");
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		return checkValidity(mExpected, act, pre, post, null, () -> assertAction(act), () -> assertPrecondition(pre),
				() -> assertPostcondInternal(post));
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
		return checkValidity(mExpected, act, pre, post, null, () -> assertAction(act), () -> assertPrecondition(pre),
				() -> assertPostcondCall(post));
	}

	@Override
	public Validity checkReturn(final IPredicate linPre, final IPredicate hierPre, final IReturnAction act,
			final IPredicate postcond) {
		return checkValidity(mExpected, act, linPre, postcond, hierPre, () -> assertAction(act),
				() -> assertPrecondition(linPre), () -> assertHierPred(hierPre), () -> assertPostcondReturn(postcond));
	}

	public boolean isLastOk() {
		return mIsLastOk;
	}

	public void setExpected(final Validity expected) {
		mExpected = expected;
	}

	@Override
	public void releaseLock() {
		clearAssertionStack();
	}

	@SafeVarargs
	private final Validity checkValidity(final Validity expected, final IAction transition, final IPredicate precond,
			final IPredicate postcond, final IPredicate precondHier, final Supplier<LBool>... funs) {
		for (final Supplier<LBool> fun : funs) {
			final LBool quickCheckResult = fun.get();
			if (quickCheckResult == LBool.UNSAT) {
				return checkValidity(expected, Validity.VALID, transition, precond, postcond, precondHier);
			}
		}
		final LBool isSat = mManagedScript.checkSat(this);
		return checkValidity(expected, IHoareTripleChecker.convertLBool2Validity(isSat), transition, precond, postcond,
				precondHier);
	}

	private Validity checkValidity(final Validity expected, final Validity actual, final IAction transition,
			final IPredicate precond, final IPredicate postcond, final IPredicate precondHier) {
		if (expected == Validity.NOT_CHECKED || expected == actual) {
			mIsLastOk = true;
			clearAssertionStack();
			return actual;
		}
		if (actual == Validity.UNKNOWN) {
			mIsLastOk = true;
			logUnsoundness(transition, precond, postcond, precondHier, expected, actual);
			clearAssertionStack();
			return actual;
		}
		mIsLastOk = false;
		logUnsoundness(transition, precond, postcond, precondHier, expected, actual);
		clearAssertionStack();
		return actual;
	}

	private void logUnsoundness(final IAction transition, final IPredicate precond, final IPredicate postcond,
			final IPredicate precondHier, final Validity expected, final Validity actual) {
		final Consumer<Object> log;
		if (actual == Validity.UNKNOWN || expected == Validity.UNKNOWN) {
			log = mLogger::warn;
		} else {
			log = mLogger::fatal;
		}

		if (actual == Validity.UNKNOWN) {
			log.accept("Soundness check inconclusive for the following hoare triple");
		} else {
			log.accept("Soundness check failed for the following hoare triple");
		}

		log.accept("Expected: " + expected + " Actual: " + actual);
		final Script script = mManagedScript.getScript();
		log.accept("Solver was " + script.getInfo(":name") + " in version " + script.getInfo(":version"));

		final List<String> strActions = getActionStrings();

		log.accept("--");
		log.accept("Pre:       {" + toString(precond) + "}");
		if (precondHier != null) {
			log.accept("PreHier:   {" + toString(precondHier) + "}");
		}
		log.accept("Action:    " + transition);
		strActions.stream().map(a -> "ActionStr: " + a).forEachOrdered(log::accept);
		log.accept("Post:      {" + toString(postcond) + "}");

		if (mGenerateUnsatCore) {
			if (actual == Validity.VALID) {
				log.accept("--");
				final Term[] unsatCore = mManagedScript.getUnsatCore(this);
				log.accept("Unsat core");
				for (final Term part : unsatCore) {
					log.accept(part.toStringDirect());
				}
			} else if (actual == Validity.INVALID) {
				log.accept("--");
				log.accept("Model of prestate for invars");
				final UnmodifiableTransFormula actTf = getAction().getTransformula();
				final ApplicationTermFinder selectFinder =
						new ApplicationTermFinder(Collections.singleton("select"), false);
				final Set<ApplicationTerm> selects = selectFinder.findMatchingSubterms(actTf.getClosedFormula());
				for (final Entry<IProgramVar, TermVariable> entry : actTf.getInVars().entrySet()) {
					final IProgramVar key = entry.getKey();
					final TermVariable tv = key.getTermVariable();
					final Term inVarConst = UnmodifiableTransFormula.getConstantForInVar(key);
					logUnsoundnessStateVar(log, selects, tv, inVarConst);
				}
				log.accept("Model of poststate for outvars");
				for (final Entry<IProgramVar, TermVariable> entry : actTf.getOutVars().entrySet()) {
					final IProgramVar key = entry.getKey();
					final TermVariable tv = key.getTermVariable();
					final Term outVarConst =
							UnmodifiableTransFormula.getConstantForOutVar(key, actTf.getInVars(), actTf.getOutVars());
					logUnsoundnessStateVar(log, selects, tv, outVarConst);
				}
			}
		} else {
			log.accept("unsat core / model generation is disabled, enable it to get more details");
		}

		if (SIMPLIFY_IF_ASSERTION_FAILS) {
			clearAssertionStack();
			log.accept("--");
			log.accept("Simplified triple ");
			log.accept("Pre:       {" + toStringSimplified(precond) + "}");
			if (precondHier != null) {
				log.accept("PreHier:   {" + toStringSimplified(precondHier) + "}");
			}
			log.accept("Action:    " + transition);
			strActions.stream().map(a -> "ActionStr: " + a).forEachOrdered(log::accept);
			log.accept("Post:      {" + toStringSimplified(postcond) + "}");
		}
	}

	private void logUnsoundnessStateVar(final Consumer<Object> log, final Set<ApplicationTerm> selects,
			final TermVariable tv, final Term varConst) {
		if (SmtUtils.isSortForWhichWeCanGetValues(tv.getSort())) {
			final Map<Term, Term> values = mManagedScript.getValue(this, new Term[] { varConst });
			log.accept(varConst + " = " + values.get(varConst).toStringDirect());
		} else if (SmtSortUtils.isArraySort(tv.getSort())) {
			selects.stream().filter(a -> a.getParameters()[0] == varConst).forEachOrdered(s -> {
				final Map<Term, Term> values = mManagedScript.getValue(this, new Term[] { s });
				log.accept(s.toStringDirect() + "=" + values.get(s).toStringDirect());
			});
		} else {
			log.accept(varConst + " = ?");
		}
	}

	private static String toString(final IPredicate pred) {
		return pred.hashCode() + "#" + pred.getClosedFormula().toStringDirect();
	}

	private List<String> getActionStrings() {
		return mAssertions.stream().filter(a -> a.getOrigin() instanceof IAction).map(a -> a.getTerm().toStringDirect())
				.collect(Collectors.toList());
	}

	private String toStringSimplified(final IPredicate pred) {
		final Term formula = pred.getFormula();
		final String pre = pred.hashCode() + "#";
		if (formula instanceof QuantifiedFormula) {
			return pre + PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, formula,
					SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION)
					.toStringDirect();
		}
		return pre
				+ SmtUtils.simplify(mManagedScript, pred.getFormula(), mServices, SimplificationTechnique.SIMPLIFY_DDA)
						.toStringDirect();
	}

	private void clearAssertionStack() {
		if (mAssertions.isEmpty()) {
			return;
		}
		final Iterator<Assertion> iter = mAssertions.iterator();
		while (iter.hasNext()) {
			iter.next();
			iter.remove();
			mManagedScript.pop(this, 1);
		}
		mHierConstants = null;
		mManagedScript.echo(this, new QuotedObject(MSG_END_EDGE_CHECK));
		mManagedScript.unlock(this);
	}

	private LBool assertAction(final IAction act) {
		if (mManagedScript.isLocked()) {
			mManagedScript.requestLockRelease();
		}
		mManagedScript.lock(this);
		mManagedScript.echo(this, new QuotedObject(MSG_START_EDGE_CHECK));

		final Supplier<Term> actSupplier = () -> {
			if (act instanceof IInternalAction) {
				return ((IInternalAction) act).getTransformula().getClosedFormula();
			} else if (act instanceof ICallAction) {
				return ((ICallAction) act).getLocalVarsAssignment().getClosedFormula();
			} else if (act instanceof IReturnAction) {
				return ((IReturnAction) act).getAssignmentOfReturn().getClosedFormula();
			} else {
				throw new AssertionError("unknown action");
			}
		};
		LBool quickCheck = pushAssertion(act, actSupplier);

		if (act instanceof IReturnAction) {
			final IReturnAction ret = (IReturnAction) act;
			final String proc = ret.getPrecedingProcedure();
			final UnmodifiableTransFormula ovaTF = mOldVarsAssignmentCache.getOldVarsAssignment(proc);

			final Supplier<Term> ovaSupplier = () -> {
				mHierConstants = new ScopedHashMap<>();
				Term ovaFormula = ovaTF.getFormula();
				// rename modifiable globals to Hier vars
				ovaFormula = renameVarsToHierConstants(ovaTF.getInVars(), ovaFormula);
				// rename oldVars of modifiable globals to default vars
				ovaFormula = renameVarsToDefaultConstants(ovaTF.getOutVars(), ovaFormula);
				assert ovaFormula.getFreeVars().length == 0;
				return mManagedScript.annotate(this, ovaFormula,
						new Annotation(ANNOT_NAMED, ID_TRANSITION_MODIFIABLE_GLOBAL_EQUALITY));
			};
			quickCheck = pushAssertion(act, ovaSupplier);

			final Supplier<Term> locVarAssignSupplier = () -> {
				final Set<IProgramVar> modifiableGlobals = ovaTF.getInVars().keySet();
				final UnmodifiableTransFormula callTf = ret.getLocalVarsAssignmentOfCall();
				Term locVarAssign = callTf.getFormula();
				// TODO: rename non-modifiable globals to DefaultConstants
				locVarAssign = renameNonModifiableGlobalsToDefaultConstants(callTf.getInVars(), modifiableGlobals,
						locVarAssign);

				// rename arguments vars to Hier vars
				locVarAssign = renameVarsToHierConstants(callTf.getInVars(), locVarAssign);
				// rename proc parameter vars to DefaultConstants
				locVarAssign = renameVarsToDefaultConstants(callTf.getOutVars(), locVarAssign);
				// rename auxiliary vars to fresh constants
				locVarAssign = renameAuxVarsToCorrespondingConstants(callTf.getAuxVars(), locVarAssign);
				assert locVarAssign.getFreeVars().length == 0;
				return mManagedScript.annotate(this, locVarAssign,
						new Annotation(ANNOT_NAMED, ID_LOCAL_VARS_ASSIGNMENT));
			};

			quickCheck = pushAssertion(act, locVarAssignSupplier);
		}
		return quickCheck;
	}

	private LBool assertPrecondition(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		LBool quickCheck = pushAssertion(p, () -> mManagedScript.annotate(this, p.getClosedFormula(),
				new Annotation(ANNOT_NAMED, ID_PRECONDITION)));
		final String predProc = getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(predProc);
		final Collection<Term> oldVarEqualities =
				constructNonModOldVarsEquality(p.getVars(), modifiableGlobals, mManagedScript, this);
		if (!oldVarEqualities.isEmpty()) {
			quickCheck = pushAssertion(p,
					() -> mManagedScript.annotate(this,
							SmtUtils.and(mManagedScript.getScript(),
									oldVarEqualities.toArray(new Term[oldVarEqualities.size()])),
							new Annotation(ANNOT_NAMED, ID_PRECONDITION_NON_MOD_GLOBAL_EQUALITY)));
		}
		return quickCheck;
	}

	private LBool assertHierPred(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		final Supplier<Term> fun = () -> {
			mHierConstants.beginScope();
			Term hierFormula = p.getFormula();

			// rename globals that are not modifiable by callee to default constants
			final String callee = getPrecedingProcedure();
			final Set<IProgramNonOldVar> modifiableGlobalsCallee =
					mModifiableGlobalVariableManager.getModifiedBoogieVars(callee);
			hierFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(p.getVars(), modifiableGlobalsCallee,
					hierFormula);

			// rename oldvars of globals that are not modifiable by caller to
			// default constants of nonOldVar
			final String caller = getSucceedingProcedure();
			final Set<IProgramNonOldVar> modifiableGlobalsCaller =
					mModifiableGlobalVariableManager.getModifiedBoogieVars(caller);
			hierFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(),
					modifiableGlobalsCaller, hierFormula, mManagedScript, this);

			// rename vars which are assigned on return to Hier vars
			hierFormula = renameVarsToHierConstants(p.getVars(), hierFormula);

			// TODO auxvars
			assert hierFormula.getFreeVars().length == 0;

			final Annotation annot = new Annotation(ANNOT_NAMED, ID_HIERACHICAL_PRECONDITION);
			return mManagedScript.annotate(this, hierFormula, annot);
		};
		return pushAssertion(p, fun);
	}

	private LBool assertPostcondInternal(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		final Supplier<Term> fun = () -> {
			// OldVars renamed (depending on modifiability)
			// All variables get index 0
			// assigned vars (locals and globals) get index 1
			// other vars get index 0
			final Term renamedFormula = constructPostcondFormula(p, getInternalAction(),
					mModifiableGlobalVariableManager, mManagedScript, this);
			assert renamedFormula.getFreeVars().length == 0;
			final Term negation = mManagedScript.term(this, "not", renamedFormula);
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_NEGATED_POSTCONDITION);
			return mManagedScript.annotate(this, negation, annot);
		};
		return pushAssertion(p, fun);
	}

	private LBool assertPostcondCall(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		final Supplier<Term> fun = () -> {
			final Set<IProgramVar> boogieVars = p.getVars();
			// rename oldVars to default constants of non-oldvars
			Term renamedFormula = renameGlobalsAndOldVarsToNonOldDefaultConstants(boogieVars, p.getFormula());
			// rename remaining variables
			renamedFormula = renameVarsToPrimedConstants(boogieVars, renamedFormula, mManagedScript, this);
			renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula, mManagedScript, this);
			assert renamedFormula.getFreeVars().length == 0;
			final Annotation annot = new Annotation(ANNOT_NAMED, ID_NEGATED_POSTCONDITION);
			return mManagedScript.annotate(this, mManagedScript.term(this, "not", renamedFormula), annot);
		};
		return pushAssertion(p, fun);
	}

	private LBool assertPostcondReturn(final IPredicate p) {
		assert mManagedScript.isLockOwner(this);
		final Supplier<Term> fun = () -> {
			mHierConstants.beginScope();

			// rename assignedVars to primed vars
			final Set<IProgramVar> assignedVars = getAssignmentOfReturn().getAssignedVars();
			Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula(), mManagedScript, this);

			final String callee = getPrecedingProcedure();
			final Set<IProgramNonOldVar> modifiableGlobalsCallee =
					mModifiableGlobalVariableManager.getModifiedBoogieVars(callee);

			// rename modifiable globals to default constants
			renamedFormula =
					renameVarsToDefaultConstants(modifiableGlobalsCallee, renamedFormula, mManagedScript, this);

			// rename globals that are not modifiable by callee to default constants
			renamedFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(p.getVars(), modifiableGlobalsCallee,
					renamedFormula);

			// rename oldvars of globals that are not modifiable by caller to
			// default constants of nonOldVar
			final String caller = getSucceedingProcedure();
			final Set<IProgramNonOldVar> modifiableGlobalsCaller =
					mModifiableGlobalVariableManager.getModifiedBoogieVars(caller);
			renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(),
					modifiableGlobalsCaller, renamedFormula, mManagedScript, this);

			// rename remaining vars to Hier vars
			renamedFormula = renameVarsToHierConstants(p.getVars(), renamedFormula);

			assert renamedFormula.getFreeVars().length == 0;

			final Annotation annot = new Annotation(ANNOT_NAMED, ID_NEGATED_POSTCONDITION);
			return mManagedScript.annotate(this, mManagedScript.term(this, "not", renamedFormula), annot);
		};
		return pushAssertion(p, fun);
	}

	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs in vars that is not contained in
	 * oldVarsOfModifiableGlobals there is an equality (= c_g c_old(g)) where c_g is the default constant of the global
	 * variable g and c_old(g) is the default constant of old(g).
	 */
	private static Collection<Term> constructNonModOldVarsEquality(final Set<IProgramVar> vars,
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

	private LBool pushAssertion(final Object origin, final Supplier<Term> formulaSupplier) {
		mManagedScript.push(this, 1);
		final Term formula = formulaSupplier.get();
		final LBool quickCheck = mManagedScript.assertTerm(this, formula);
		mAssertions.push(new Assertion(formula, origin, quickCheck));
		return quickCheck;
	}

	private static Term constructPostcondFormula(final IPredicate p, final IInternalAction action,
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

	private IAction getAction() {
		final Optional<Assertion> result =
				mAssertions.stream().filter(a -> a.getOrigin() instanceof IAction).findFirst();
		if (result.isPresent()) {
			return (IAction) result.get().getOrigin();
		}
		throw new AssertionError("No action");
	}

	private IInternalAction getInternalAction() {
		final IAction action = getAction();
		if (action instanceof IInternalAction) {
			return (IInternalAction) action;
		}
		throw new AssertionError("No internal action");
	}

	private String getSucceedingProcedure() {
		return getAction().getSucceedingProcedure();
	}

	private String getPrecedingProcedure() {
		return getAction().getPrecedingProcedure();
	}

	private UnmodifiableTransFormula getAssignmentOfReturn() {
		final IAction action = getAction();
		if (action instanceof IReturnAction) {
			return ((IReturnAction) action).getAssignmentOfReturn();
		}
		throw new AssertionError("No return action");
	}

	private static final class Assertion {
		private final Term mTerm;
		private final Object mOrigin;
		private final LBool mResult;

		public Assertion(final Term term, final Object origin, final LBool quickCheckResult) {
			mTerm = term;
			mOrigin = origin;
			mResult = quickCheckResult;
		}

		public Term getTerm() {
			return mTerm;
		}

		public Object getOrigin() {
			return mOrigin;
		}

		public LBool getResult() {
			return mResult;
		}
	}

}
