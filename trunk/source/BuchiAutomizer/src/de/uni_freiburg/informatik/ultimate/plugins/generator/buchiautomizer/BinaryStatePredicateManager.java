/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;

public class BinaryStatePredicateManager {

	private static final boolean SIMPLIFY_SUPPORTING_INVARIANTS = true;
	private static final boolean ANNOTATE = false;

	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final IProgramNonOldVar mUnseededVariable;
	private final IProgramNonOldVar[] mOldRankVariables;

	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * True if predicates have been computed. False if predicates have been cleared or predicates have never been
	 * computed so far.
	 */
	private boolean mProvidesPredicates;

	private IPredicate mStemPrecondition;
	private IPredicate mStemPostcondition;
	private IPredicate mSiConjunction;
	private IPredicate mHonda;
	private Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;
	private IPredicate mRankEqualityAndSi;
	private IPredicate mRankEquality;
	private IPredicate mRankDecreaseAndBound;

	private TerminationArgument mTerminationArgument;

	private Term[] mLexTerms;
	private IPredicate[] mLexEquality;
	private IPredicate[] mLexDecrease;

	/**
	 * Is the loop also terminating without the stem?
	 */
	private Boolean mLoopTermination;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public BinaryStatePredicateManager(final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IProgramNonOldVar unseededVariable, final IProgramNonOldVar[] oldRankVariables,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mScript = csToolkit.getManagedScript().getScript();
		mPredicateFactory = predicateFactory;
		mManagedScript = csToolkit.getManagedScript();
		mCsToolkit = csToolkit;

		mUnseededVariable = unseededVariable;
		mOldRankVariables = oldRankVariables;
	}

	public boolean providesPredicates() {
		return mProvidesPredicates;
	}

	public boolean isLoopWithoutStemTerminating() {
		assert mProvidesPredicates;
		return mLoopTermination;
	}

	public TerminationArgument getTerminationArgument() {
		assert mProvidesPredicates;
		return mTerminationArgument;
	}

	/**
	 * Compute IPredicate that states that the current value of the ranking function f is smaller than or equal to the
	 * value of oldrank. I.e., (f_0,...f_n) <=_lex (oldrk_0,...,oldrk_n)
	 */
	public IPredicate getRankEquality() {
		return mRankEquality;
	}

	/**
	 * Compute IPredicate that states that the current value of the ranking function f is strictly smaller than the
	 * value of oldrank and bounded from below. We use a formula similar to (f_0,...f_n) <_lex (oldrk_0,...,oldrk_n)
	 * with the additional constraint that for the decreasing component oldrk_i>=0 holds.
	 */
	public IPredicate getRankDecreaseAndBound() {
		return mRankDecreaseAndBound;
	}

	public IPredicate getStemPrecondition() {
		assert mProvidesPredicates;
		return mStemPrecondition;
	}

	public IPredicate getStemPostcondition() {
		assert mProvidesPredicates;
		return mStemPostcondition;
	}

	public IPredicate getSiConjunction() {
		assert mProvidesPredicates;
		return mSiConjunction;
	}

	@Deprecated
	public IPredicate getHondaPredicate() {
		assert mProvidesPredicates;
		return mHonda;
	}

	@Deprecated
	public IPredicate getRankEqAndSi() {
		assert mProvidesPredicates;
		return mRankEqualityAndSi;
	}

	public IProgramNonOldVar getUnseededVariable() {
		assert mProvidesPredicates;
		return mUnseededVariable;
	}

	public IProgramNonOldVar[] getOldRankVariables() {
		assert mProvidesPredicates;
		return mOldRankVariables;
	}

	public void clearPredicates() {
		if (!mProvidesPredicates) {
			throw new AssertionError("no predicates provided cannot clear");
		}
		mLoopTermination = null;
		mTerminationArgument = null;
		mStemPrecondition = null;
		mStemPostcondition = null;
		mSiConjunction = null;
		mHonda = null;
		mRankEqualityAndSi = null;
		mRankEquality = null;
		mRankDecreaseAndBound = null;
		mProvidesPredicates = false;
		mLexDecrease = null;
		mLexEquality = null;
		mLexTerms = null;
		mModifiableGlobalsAtHonda = null;
	}

	/**
	 * @param loopTermination
	 * @param termArg
	 * @param removeSuperfluousSupportingInvariants
	 * @param loopTf
	 *            TransFormula for loop, has to be provided if we remove superfluous supporting invariants.
	 * @param loopTf
	 * @param modifiableGlobals
	 * @param loop
	 * @param stem
	 * @param loop
	 * @param stem
	 */
	public void computePredicates(final boolean loopTermination, final TerminationArgument termArg,
			final boolean removeSuperfluousSupportingInvariants, final UnmodifiableTransFormula stemTf,
			final UnmodifiableTransFormula loopTf, final Set<IProgramNonOldVar> modifiableGlobals) {
		assert mLoopTermination == null;
		assert mTerminationArgument == null;
		assert mStemPrecondition == null;
		assert mStemPostcondition == null;
		assert mHonda == null;
		assert mRankEqualityAndSi == null;
		assert mRankEquality == null;
		assert mRankDecreaseAndBound == null;
		assert mLexDecrease == null;
		assert mLexEquality == null;
		assert mLexTerms == null;
		assert mModifiableGlobalsAtHonda == null;
		// assert modifiableGlobalsAtHonda.contains(mUnseededVariable) : "unseeded var may be modified by each
		// procedure";
		mLoopTermination = loopTermination;
		mTerminationArgument = termArg;
		final IPredicate unseededPredicate = unseededPredicate();
		mStemPrecondition = unseededPredicate;
		mModifiableGlobalsAtHonda = modifiableGlobals;

		final RankingFunction rf = mTerminationArgument.getRankingFunction();
		decodeLex(rf);
		mRankEquality = computeRankEquality();
		mRankDecreaseAndBound = computeRankDecreaseAndBound();
		mSiConjunction = computeSiConjunction(mTerminationArgument.getSupportingInvariants(),
				mTerminationArgument.getArrayIndexSupportingInvariants(), removeSuperfluousSupportingInvariants, stemTf,
				loopTf, modifiableGlobals);
		final boolean siConjunctionIsTrue = isTrue(mSiConjunction);
		if (siConjunctionIsTrue) {
			mStemPostcondition = unseededPredicate;
		} else {
			mStemPostcondition = mPredicateFactory.and(unseededPredicate, mSiConjunction);
		}
		if (siConjunctionIsTrue) {
			mRankEqualityAndSi = mRankEquality;
		} else {
			mRankEqualityAndSi = mPredicateFactory.and(mRankEquality, mSiConjunction);
		}
		IPredicate unseededOrRankDecrease;

		unseededOrRankDecrease = mPredicateFactory.or(unseededPredicate, mRankDecreaseAndBound);

		if (siConjunctionIsTrue) {
			mHonda = unseededOrRankDecrease;
		} else {
			mHonda = mPredicateFactory.and(mSiConjunction, unseededOrRankDecrease);
		}
		mProvidesPredicates = true;
	}

	private List<Term> removeSuperfluousSupportingInvariants(final List<Term> siTerms,
			final UnmodifiableTransFormula loopTf, final Set<IProgramNonOldVar> modifiableGlobals) {
		final ArrayList<Term> neededSiTerms = new ArrayList<>();
		for (int i = 0; i < siTerms.size(); i++) {
			final Term[] siTermSubset = startingFromIPlusList(siTerms, i + 1, neededSiTerms);
			final boolean isSi = isSupportingInvariant(siTermSubset, loopTf, modifiableGlobals);
			if (!isSi) {
				// we cannot drop the i'th term
				neededSiTerms.add(siTerms.get(i));
			}
		}
		final int superfluous = siTerms.size() - neededSiTerms.size();
		mLogger.info(superfluous + " out of " + siTerms.size()
				+ " supporting invariants were superfluous and have been removed");
		return neededSiTerms;
	}

	private boolean isSupportingInvariant(final Term[] siTermSubset, final UnmodifiableTransFormula loopTf,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		final List<Term> siSubsetAndRankEqualityList = new ArrayList<>(Arrays.asList(siTermSubset));
		siSubsetAndRankEqualityList.add(mRankEquality.getFormula());
		final IPredicate siSubsetAndRankEquality =
				mPredicateFactory.newPredicate(SmtUtils.and(mScript, siSubsetAndRankEqualityList));

		final List<Term> siSubsetAndRankDecreaseAndBoundList = new ArrayList<>(Arrays.asList(siTermSubset));
		siSubsetAndRankDecreaseAndBoundList.add(mRankDecreaseAndBound.getFormula());
		final IPredicate siSubsetAndRankDecreaseAndBound =
				mPredicateFactory.newPredicate(SmtUtils.and(mScript, siSubsetAndRankDecreaseAndBoundList));
		final LBool sat = PredicateUtils.isInductiveHelper(mScript, siSubsetAndRankEquality,
				siSubsetAndRankDecreaseAndBound, loopTf, modifiableGlobals, modifiableGlobals);
		switch (sat) {
		case SAT:
		case UNKNOWN:
			return false;
		case UNSAT:
			return true;
		default:
			throw new AssertionError("unknown case");
		}
	}

	private boolean assertSupportingInvariant(final Term[] siTermSubset, final UnmodifiableTransFormula loopTf,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		final List<Term> siSubsetAndRankEqualityList = new ArrayList<>(Arrays.asList(siTermSubset));
		siSubsetAndRankEqualityList.add(mRankEquality.getFormula());
		final IPredicate siSubsetAndRankEquality =
				mPredicateFactory.newPredicate(SmtUtils.and(mScript, siSubsetAndRankEqualityList));

		final List<Term> siSubsetAndRankDecreaseAndBoundList = new ArrayList<>(Arrays.asList(siTermSubset));
		siSubsetAndRankDecreaseAndBoundList.add(mRankDecreaseAndBound.getFormula());
		final List<Term> siSubsetAndRankDecreaseAndBoundConjunctsList = new ArrayList<>();
		for (final Term succTerm : siSubsetAndRankDecreaseAndBoundList) {
			siSubsetAndRankDecreaseAndBoundConjunctsList.addAll(Arrays.asList(SmtUtils.getConjuncts(succTerm)));
		}
		for (final Term succTerm : siSubsetAndRankDecreaseAndBoundConjunctsList) {
			final IPredicate succPred = mPredicateFactory.newPredicate(succTerm);
			final LBool sat = PredicateUtils.isInductiveHelper(mScript, siSubsetAndRankEquality, succPred, loopTf,
					modifiableGlobals, modifiableGlobals);
			if (sat != LBool.UNSAT) {
				throw new AssertionError("Incorrect supporting invariant. Not inductive: " + succTerm);
			}
		}
		return true;
	}

	/**
	 * Returns an array that contains all elements of list with index greater than or equal to i and all elements of the
	 * list additionalList.
	 *
	 * @return
	 */
	static Term[] startingFromIPlusList(final List<Term> list, final int i, final List<Term> additionalList) {
		final List<Term> result = new ArrayList<>(list.size() + i + list.size());
		for (int j = i; j < list.size(); j++) {
			result.add(list.get(j));
		}
		result.addAll(additionalList);
		return result.toArray(new Term[result.size()]);
	}

	private IPredicate unseededPredicate() {
		final Set<IProgramVar> vars = new HashSet<>(1);
		vars.add(mUnseededVariable);
		final Term formula = mUnseededVariable.getTermVariable();
		final IPredicate result = mPredicateFactory.newPredicate(formula);
		return result;
	}

	private IPredicate computeSiConjunction(final Collection<SupportingInvariant> siList, final Collection<Term> aisi,
			final boolean removeSuperfluousSupportingInvariants, final UnmodifiableTransFormula stemTf,
			final UnmodifiableTransFormula loopTf, final Set<IProgramNonOldVar> modifiableGlobals) {
		List<Term> siTerms = new ArrayList<>(siList.size() + aisi.size());
		for (final SupportingInvariant si : siList) {
			final Term formula = si.asTerm(mManagedScript.getScript());
			siTerms.add(formula);
		}
		siTerms.addAll(aisi);
		if (!impliedByStem(stemTf, siTerms, modifiableGlobals)) {
			final String stemSize = new DagSizePrinter(stemTf.getFormula()).toString();
			throw new AssertionError("Supporting invariant not implied by stem. Stem size: " + stemSize);
		}
		if (removeSuperfluousSupportingInvariants) {
			assert assertSupportingInvariant(siTerms.toArray(new Term[siTerms.size()]), loopTf, modifiableGlobals);
			siTerms = removeSuperfluousSupportingInvariants(siTerms, loopTf, modifiableGlobals);
			assert assertSupportingInvariant(siTerms.toArray(new Term[siTerms.size()]), loopTf, modifiableGlobals);
		}

		final Term conjunction = SmtUtils.and(mScript, siTerms);
		final Term si;
		if (SIMPLIFY_SUPPORTING_INVARIANTS) {
			final Term simplified = SmtUtils.simplify(mManagedScript, conjunction, mServices, mSimplificationTechnique);
			final Term normalized = new AffineSubtermNormalizer(mManagedScript.getScript()).transform(simplified);
			si = normalized;
			if (SmtUtils.isFalseLiteral(si)) {
				throw new AssertionError(
						"Supporting invariant is false. This is impossible since we only consider feasible stems.");
			}
		} else {
			si = conjunction;
		}
		return mPredicateFactory.newPredicate(si);
	}

	private boolean impliedByStem(final UnmodifiableTransFormula stemTf, final List<Term> siTerms,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		final ArrayList<Term> implied = new ArrayList<>();
		final ArrayList<Term> notImplied = new ArrayList<>();
		for (final Term siTerm : siTerms) {
			final boolean isInductive = isInductive(Collections.singleton(mManagedScript.getScript().term("true")),
					modifiableGlobals, stemTf, Collections.singleton(siTerm), modifiableGlobals);
			if (isInductive) {
				implied.add(siTerm);
			} else {
				notImplied.add(siTerm);
			}
		}
		assert notImplied.isEmpty() : "The following invariants are not implied by stem " + notImplied.toString();
		return notImplied.isEmpty();
	}

	private boolean isInductive(final Set<Term> precondition, final Set<IProgramNonOldVar> modifiableGlobals,
			final UnmodifiableTransFormula transFormula, final Set<Term> postcondition,
			final Set<IProgramNonOldVar> modifiableGlobals2) {
		final IPredicate precondPredicate = mPredicateFactory.newPredicate(SmtUtils.and(mScript, precondition));
		final IPredicate postcondPredicate = mPredicateFactory.newPredicate(SmtUtils.and(mScript, postcondition));
		final LBool sat = PredicateUtils.isInductiveHelper(mManagedScript.getScript(), precondPredicate,
				postcondPredicate, transFormula, modifiableGlobals, modifiableGlobals2);
		return sat == LBool.UNSAT;
	}

	public IPredicate supportingInvariant2Predicate(final SupportingInvariant si) {
		Term formula = si.asTerm(mManagedScript.getScript());
		formula = SmtUtils.simplify(mManagedScript, formula, mServices, mSimplificationTechnique);
		return term2Predicate(formula);
	}

	public IPredicate term2Predicate(final Term term) {
		final IPredicate result = mPredicateFactory.newPredicate(term);
		return result;
	}

	/**
	 * Given a RankingFunction with lex terms (f_0, ..., f_n), initialize the array mLexEquality with the terms
	 * (oldrank_0 >= f_0, ..., oldrank_n >= f_n) and initialize the array mLexDecrease with the terms (oldrank_0 > f_0
	 * &&, ..., oldrank_n > f_n).
	 */
	private void decodeLex(final RankingFunction rf) {
		mLexTerms = rf.asLexTerm(mScript);
		mLexEquality = new IPredicate[mLexTerms.length];
		for (int i = 0; i < mLexTerms.length; i++) {
			mLexEquality[i] = getRankInEquality(mLexTerms[i], ">=", mOldRankVariables[i], false);
			if (ANNOTATE) {
				final String name = "equality" + i;
				final Annotation annot = new Annotation(":named", name);
				mLexTerms[i] = mScript.annotate(mLexTerms[i], annot);
			}
		}
		mLexDecrease = new IPredicate[mLexTerms.length];
		for (int i = 0; i < mLexTerms.length; i++) {
			mLexDecrease[i] = getRankInEquality(mLexTerms[i], ">", mOldRankVariables[i], true);
			if (ANNOTATE) {
				final String name = "strictDecrease" + i;
				final Annotation annot = new Annotation(":named", name);
				mLexTerms[i] = mScript.annotate(mLexTerms[i], annot);
			}
		}
	}

	private IPredicate computeRankEquality() {
		final IPredicate result = mPredicateFactory.and(mLexEquality);
		return result;
	}

	private IPredicate computeRankDecreaseAndBound() {
		final IPredicate[] disjuncts = new IPredicate[mLexTerms.length];
		for (int i = 0; i < mLexTerms.length; i++) {
			final IPredicate[] conjuncts = new IPredicate[i + 1];
			System.arraycopy(mLexEquality, 0, conjuncts, 0, i);
			conjuncts[i] = mLexDecrease[i];
			disjuncts[i] = mPredicateFactory.and(conjuncts);
		}

		final IPredicate result = mPredicateFactory.or(disjuncts);
		return result;
	}

	private IPredicate getRankInEquality(final Term rfTerm, final String symbol, final IProgramVar oldRankVariable,
			final boolean addGeq0) {
		assert symbol.equals(">=") || symbol.equals(">");

		Term equality = mScript.term(symbol, oldRankVariable.getTermVariable(), rfTerm);
		if (addGeq0) {
			equality = SmtUtils.and(mScript, equality, getRankGeq0(oldRankVariable));
		}

		final IPredicate result = mPredicateFactory.newPredicate(equality);
		return result;
	}

	private Term getRankGeq0(final IProgramVar oldRankVariable) {
		final Term geq = mScript.term(">=", oldRankVariable.getTermVariable(),
				SmtUtils.constructIntValue(mScript, BigInteger.ZERO));
		return geq;
	}

	public boolean checkSupportingInvariant(IPredicate siPredicate, final NestedWord<? extends IIcfgTransition<?>> stem,
			final NestedWord<? extends IAction> loop, final ModifiableGlobalsTable modifiableGlobalsTable) {
		boolean result = true;
		final IPredicate truePredicate = mPredicateFactory.newPredicate(mManagedScript.getScript().term("true"));
		if (isTrue(siPredicate)) {
			siPredicate = truePredicate;
		}
		final LBool stemCheck = createTraceCheck(truePredicate, siPredicate, stem).isCorrect();
		if (stemCheck != LBool.UNSAT) {
			result = false;
		}
		final LBool loopCheck = createTraceCheck(siPredicate, siPredicate, stem).isCorrect();
		if (loopCheck != LBool.UNSAT) {
			result = false;
		}
		return result;
	}

	public boolean checkRankDecrease(final NestedWord<? extends IIcfgTransition<?>> loop,
			final ModifiableGlobalsTable modifiableGlobalsTable) {
		return createTraceCheck(mRankEqualityAndSi, mRankDecreaseAndBound, loop).isCorrect() == LBool.UNSAT;
	}

	private ITraceCheck createTraceCheck(final IPredicate preCond, final IPredicate postCond,
			final NestedWord<? extends IIcfgTransition<?>> trace) {
		return new TraceCheck<>(preCond, postCond, new TreeMap<Integer, IPredicate>(), trace, mServices, mCsToolkit,
				AssertCodeBlockOrder.NOT_INCREMENTALLY, false, false);

	}

	private static boolean isTrue(final IPredicate pred) {
		final Term term = pred.getFormula();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("true")) {
				return true;
			}
		}
		return false;
	}

	public boolean containsOldRankVariable(final IPredicate pred) {
		for (final IProgramVar rankVariable : getOldRankVariables()) {
			if (pred.getVars().contains(rankVariable)) {
				return true;
			}
		}
		return false;
	}

}
