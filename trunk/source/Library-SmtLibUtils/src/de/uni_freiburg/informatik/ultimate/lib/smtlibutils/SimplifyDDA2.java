/*
 * Copyright (C) 2023 Xinyu Jiang
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.DescendResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.TermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolyPoNeUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.Context;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.Context.CcTransformation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
//import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SimplificationTest;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * @author Xinyu Jiang
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SimplifyDDA2 extends TermWalker<Term> {
	/**
	 * Replace terms of the form `x = l ∧ φ(x)` by `x = l ∧ φ(l)` and replace terms of the form `x ≠ l ∨ φ(x)` by `x ≠ l
	 * ∨ φ(l)`, where l is a literal (of sort Real, Int, or BitVec) and x is a variable in a {@link PolynomialRelation}
	 * (E.g., a {@link TermVariable}, a constant symbol (0-ary function symbol), a select term `(select a k)`.)
	 */
	private static final boolean APPLY_CONSTANT_FOLDING = false;
	private static final boolean DEBUG_CHECK_RESULT = false;
	// private static final boolean PREPROCESS_WITH_POLY_PAC_SIMPLIFICATION = false;
	// private static final boolean CHECK_ALL_NODES_FOR_REDUNDANCY = false;
	private static final boolean DESCEND_INTO_QUANTIFIED_FORMULAS = false;
	private static final boolean OVERAPROXIMATE_QUANTIFIED_FORMULAS_IN_CONTEXT = true;
	private static final boolean SIMPLIFY_REPEATEDLY = true;
	private static final CheckedNodes test = CheckedNodes.ALL_NODES;

	private enum CheckedNodes {
		ONLY_LEAVES, ALL_NODES, ONLY_LEAVES_AND_QUANTIFIED_NODES
	}

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private int mAssertionStackHeight = 0;
	private int mNumberOfCheckSatCommands = 0;
	private int mNonConstrainingNodes = 0;
	private int mNonRelaxingNodes = 0;
	private long mCheckSatTime = 0;
	private final long mStartTime = System.nanoTime();
	private final ScopedHashMap<TermVariable, TermVariable> mRenamingMap;
	private boolean mPreviousWasQuantified = false;

	private SimplifyDDA2(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		super();
		mServices = services;
		mMgdScript = mgdScript;
		mRenamingMap = new ScopedHashMap<>();
	}

	@Override
	protected Term constructContextForApplicationTerm(final Term context, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam) {
		// 20230629 Matthias: In our meeting, I said that we can copy&paste this method
		// from PolyPacSimplification. I forgot that in an optimized version of this
		// simplification we want to use the push/pop SMT commands and assert conjuncts of
		// the critical constraint as soon as possible.
		final List<Term> otherParams = new ArrayList<>(allParams);
		otherParams.remove(selectedParam);

		if (!mPreviousWasQuantified) {
			mMgdScript.getScript().pop(1);
			mAssertionStackHeight--;
		} else {
			mPreviousWasQuantified = false;
		}

		mMgdScript.getScript().push(1);
		mAssertionStackHeight++;

		final List<Term> newParams = new ArrayList<>();
		if (symb.getName().equals("and")) {
			for (final Term otherParam : otherParams) {
				if (!OVERAPROXIMATE_QUANTIFIED_FORMULAS_IN_CONTEXT || QuantifierUtils.isQuantifierFree(otherParam)) {
					mMgdScript.getScript().assertTerm(otherParam);
					newParams.add(otherParam);
				}
			}
		}

		if (symb.getName().equals("or")) {
			for (final Term otherParam : otherParams) {
				if (!OVERAPROXIMATE_QUANTIFIED_FORMULAS_IN_CONTEXT || QuantifierUtils.isQuantifierFree(otherParam)) {
					mMgdScript.getScript().assertTerm(SmtUtils.not(mMgdScript.getScript(), otherParam));
					newParams.add(SmtUtils.not(mMgdScript.getScript(), otherParam));
				}
			}
			// TODO Matthias 20230726: following method to find out whether formula contains quantifiers
			// QuantifierUtils.isQuantifierFree()
		}
		return SmtUtils.and(mMgdScript.getScript(), newParams);
		// return null;
		// return Context.buildCriticalConstraintForConDis(mServices, mMgdScript, context, symb, allParams,
		// selectedParam, CcTransformation.TO_NNF);
	}

	@Override
	protected Term constructContextForQuantifiedFormula(final Term context, final int quant,
			final List<TermVariable> vars) {
		// 20230629 Matthias: In our meeting, I said that we can copy&paste this method
		// from PolyPacSimplification. I forgot that in an optimized version of this
		// simplification we want to use the push/pop SMT commands and assert conjuncts of
		// the critical constraint as soon as possible.
		return Context.buildCriticalContraintForQuantifiedFormula(mMgdScript.getScript(), context, vars,
				CcTransformation.TO_NNF);
	}

	/**
	 * Checks if the current node is a leaf, i.e., if we are at a atomic formula, or at a negated atomic formula.
	 */
	private static boolean isLeaf(final Term term) {
		if (term instanceof QuantifiedFormula) {
			return false;
		}
		final Term suformulaOfNegation = SmtUtils.unzipNot(term);
		if (suformulaOfNegation != null) {
			return SmtUtils.isAtomicFormula(suformulaOfNegation);
		} else {
			return SmtUtils.isAtomicFormula(term);
		}
	}

	/**
	 * Checks if the critical constraint implies the formula(or its negation), and returns `true`(`false`) for ascend.
	 * returns null if neither is the case
	 */
	private DescendResult checkRedundancy(final Term term) {
		final Term result;
		final long timeBeforeConstrainigcheck = System.nanoTime();
		mNumberOfCheckSatCommands++;
		final LBool isNonConstraining =
				Util.checkSat(mMgdScript.getScript(), SmtUtils.not(mMgdScript.getScript(), term));
		mCheckSatTime += (System.nanoTime() - timeBeforeConstrainigcheck);
		if (isNonConstraining == LBool.UNSAT) {
			mNonConstrainingNodes++;
			result = mMgdScript.getScript().term("true");
			return new TermContextTransformationEngine.FinalResultForAscend(result);
		}
		mNumberOfCheckSatCommands++;
		final long timeBeforeRelaxingcheck = System.nanoTime();
		final LBool isNonRelaxing = Util.checkSat(mMgdScript.getScript(), term);
		mCheckSatTime += (System.nanoTime() - timeBeforeRelaxingcheck);
		if (isNonRelaxing == LBool.UNSAT) {
			mNonRelaxingNodes++;
			result = mMgdScript.getScript().term("false");
			return new TermContextTransformationEngine.FinalResultForAscend(result);
		}
		return null;
	}

	private DescendResult descendIntoQuantifiedFormula(final QuantifiedFormula term) {
		mPreviousWasQuantified = true;
		final QuantifiedFormula termAsQuantifiedFormula = term;
		mRenamingMap.beginScope();
		mMgdScript.lock(this);
		final ArrayList<TermVariable> substitutedTermVariables = new ArrayList<>();
		for (final TermVariable quantifiedVariable : termAsQuantifiedFormula.getVariables()) {
			final TermVariable freshVariable = mMgdScript.constructFreshCopy(quantifiedVariable);
			mRenamingMap.put(quantifiedVariable, freshVariable);
			substitutedTermVariables.add(freshVariable);
			mMgdScript.declareFun(this, freshVariable.getName(), new Sort[0], freshVariable.getSort());
		}
		mMgdScript.unlock(this);

		final Term substitutedSubformula =
				Substitution.apply(mMgdScript, mRenamingMap, termAsQuantifiedFormula.getSubformula());
		final QuantifiedFormula substitutedQuantifiedFormula =
				(QuantifiedFormula) SmtUtils.quantifier(mMgdScript.getScript(), termAsQuantifiedFormula.getQuantifier(),
						substitutedTermVariables, substitutedSubformula);
		return new TermContextTransformationEngine.IntermediateResultForDescend(substitutedQuantifiedFormula);
	}

	private boolean checkRedundancyForNode(final Term term) {
		return ((test == CheckedNodes.ALL_NODES)
				|| ((test == CheckedNodes.ONLY_LEAVES_AND_QUANTIFIED_NODES)
						&& (term instanceof QuantifiedFormula || isLeaf(term)))
				|| (test == CheckedNodes.ONLY_LEAVES && isLeaf(term)));
	}

	@Override
	protected DescendResult convert(final Term context, final Term term) {
		// The following is copy&pase of an optimization for the PolyPacSimplification.
		// Maybe we wont to have that optimization too, maybe its useless.
		if (APPLY_CONSTANT_FOLDING) {
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final Term conjunct : SmtUtils.getConjuncts(context)) {
				if (!SmtUtils.isFunctionApplication(conjunct, "=")) {
					continue;
				}
				final PolynomialRelation polyRel = PolynomialRelation.of(mMgdScript.getScript(), conjunct);
				if (polyRel != null) {
					final SolvedBinaryRelation sbr = polyRel.isSimpleEquality(mMgdScript.getScript());
					if (sbr != null) {
						substitutionMapping.put(sbr.getLeftHandSide(), sbr.getRightHandSide());
					}
				}
			}
			if (!substitutionMapping.isEmpty()) {
				final Term renamed = Substitution.apply(mMgdScript, substitutionMapping, term);
				if (renamed != term) {
					return new TermContextTransformationEngine.FinalResultForAscend(renamed);
				}
			}
		}

		// 20230629 Matthias: The TermWalker does a depth-first traversal through the
		// formula. It calls this method on each node while descending from the root to the
		// leaves.
		// The method may return the following for some term t if we want to consider
		// this term as a leaf of the formula tree and t is the result of its
		// simplification.
		// new TermContextTransformationEngine.FinalResultForAscend(t);
		// The method may return the following for some term t if we want to descend
		// further into t. Here, t may be the input term of some modification of t
		// new TermContextTransformationEngine.IntermediateResultForDescend(term);

		if (SmtUtils.isFalseLiteral(context)) {
			throw new AssertionError("critical constraint is false");
		}
		DescendResult result;
		final boolean descend = (DESCEND_INTO_QUANTIFIED_FORMULAS && term instanceof QuantifiedFormula)
				|| !(isLeaf(term) || term instanceof QuantifiedFormula);
		if (checkRedundancyForNode(term) && ((result = checkRedundancy(term)) != null)) {
			return result;
		} else if (descend) {

			if (DESCEND_INTO_QUANTIFIED_FORMULAS && term instanceof QuantifiedFormula) {
				return descendIntoQuantifiedFormula((QuantifiedFormula) term);
			} else {
				mMgdScript.getScript().push(1);
				mAssertionStackHeight++;
				return new TermContextTransformationEngine.IntermediateResultForDescend(term);
			}
		} else {
			return new TermContextTransformationEngine.FinalResultForAscend(term);
		}

		// The following is copy&paste of an optimization for the PolyPacSimplification.
		// Maybe we wont to have that optimization too, maybe its useless.
		// if (term instanceof ApplicationTerm) {
		// final ApplicationTerm appTerm = (ApplicationTerm) term;
		// if (appTerm.getFunction().getName().equals("and") || appTerm.getFunction().getName().equals("or")) {
		// if (SmtUtils.isFalseLiteral(context)) {
		// Optimization for cases in which context is "false"
		// TODO 20210802 Matthias: check if this optimization
		// is still needed
		// final Term result;
		// if (appTerm.getFunction().getName().equals("and")) {
		// result = mMgdScript.getScript().term("true");
		// } else if (appTerm.getFunction().getName().equals("or")) {
		// result = mMgdScript.getScript().term("false");
		// } else {
		// throw new AssertionError();
		// }
		// return new TermContextTransformationEngine.FinalResultForAscend(result);
		// } else {
		// return new TermContextTransformationEngine.IntermediateResultForDescend(term);
		// }
		// }
		// }

		// return new TermContextTransformationEngine.FinalResultForAscend(term);
	}

	//// always push pop for everything
	@Override
	protected Term constructResultForApplicationTerm(final Term context, final ApplicationTerm originalApplicationTerm,
			final Term[] resultParams) {
		if (!mPreviousWasQuantified) {
			mMgdScript.getScript().pop(1);
			mAssertionStackHeight--;
		} else {
			mPreviousWasQuantified = false;
		}

		assert mAssertionStackHeight >= 0;
		// While descending from node back to its parents, this method is called.
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			final CondisDepthCode contextCdc = CondisDepthCode.of(context);
			throw new ToolchainCanceledException(this.getClass(),
					String.format("simplifying %s xjuncts wrt. a %s context", resultParams.length, contextCdc));
		}
		if (originalApplicationTerm.getFunction().getName().equals("and")) {
			return PolyPoNeUtils.and(mMgdScript.getScript(), context, Arrays.asList(resultParams));
		}
		if (originalApplicationTerm.getFunction().getName().equals("or")) {
			return PolyPoNeUtils.or(mMgdScript.getScript(), context, Arrays.asList(resultParams));
		}
		throw new AssertionError();
	}

	public static Term simplify(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term term) {
		// 20230629 Matthias: The constructor of this class is private. Uses should call
		// this simplification via this static method.
		final Term result = simplify(services, mgdScript, mgdScript.getScript().term("true"), term);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			SmtUtils.checkLogicalEquivalenceForDebugging(mgdScript.getScript(), result, term, PolyPoNeUtils.class,
					tolerateUnknown);
		}
		return result;
	}

	public static Term simplify(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term context, final Term term) {
		// 20230629 Matthias: The constructor of this class is private. Uses should call
		// this simplification via this static method.
		final Term result;
		final SimplifyDDA2 simplifyDDA2 = new SimplifyDDA2(services, mgdScript);
		try {
			final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(term);
			final Comparator<Term> siblingOrder = null;
			// TODO Matthias 20230810: Some example for an order in the next line.
			// final Comparator<Term> siblingOrder = new TreeSizeComperator(CommuhashUtils.HASH_BASED_COMPERATOR);
			result = TermContextTransformationEngine.transform(simplifyDDA2, siblingOrder, context, nnf);
			final ILogger logger = services.getLoggingService().getLogger(SimplifyDDA2.class);
			if (logger.isInfoEnabled()) {
				logger.info(simplifyDDA2.generateExitMessage());
			}
			final int stackHeight = simplifyDDA2.getAssertionStackHeight();
			if (stackHeight != 0) {
				throw new AssertionError(String.format("stackHeight is non-zero"));
			}
		} catch (final ToolchainCanceledException tce) {
			simplifyDDA2.clearStack();
			final CondisDepthCode termCdc = CondisDepthCode.of(term);
			final String taskDescription = String.format("simplifying a %s term", termCdc);
			tce.addRunningTaskInfo(new RunningTaskInfo(SimplifyDDA2.class, taskDescription));
			throw tce;
		}
		return result;
	}

	public int getAssertionStackHeight() {
		return mAssertionStackHeight;
	}

	public void clearStack() {
		while (mAssertionStackHeight > 0) {
			mMgdScript.getScript().pop(1);
			mAssertionStackHeight--;
		}
	}

	public String generateExitMessage() {
		return String.format(
				"Run SimplifyDDA2 in %s ms. %s check-sat commands took %s ms. %s non-constraining nodes. %s Non-relaxing nodes.",
				(System.nanoTime() - mStartTime) / 1000000, mNumberOfCheckSatCommands, mCheckSatTime / 1000000,
				mNonConstrainingNodes, mNonRelaxingNodes);
	}

	@Override
	protected Term constructResultForQuantifiedFormula(final Term context,
			final QuantifiedFormula originalQuantifiedFormula, final Term resultSubformula) {

		if (DESCEND_INTO_QUANTIFIED_FORMULAS) {
			final HashMap<TermVariable, TermVariable> swapped = new HashMap<>();
			final ArrayList<TermVariable> revertedTermVariables = new ArrayList<>();
			for (final Map.Entry<TermVariable, TermVariable> entry : mRenamingMap.currentScopeEntries()) {
				swapped.put(entry.getValue(), entry.getKey());
				revertedTermVariables.add(entry.getKey());
			}
			final Term revertedSubformula = Substitution.apply(mMgdScript, swapped, resultSubformula);
			mRenamingMap.endScope();
			mMgdScript.getScript().pop(1);
			mAssertionStackHeight--;
			assert mAssertionStackHeight >= 0;
			return SmtUtils.quantifier(mMgdScript.getScript(), originalQuantifiedFormula.getQuantifier(),
					revertedTermVariables, revertedSubformula);
		}
		mMgdScript.getScript().pop(1);
		mAssertionStackHeight--;
		assert mAssertionStackHeight >= 0;
		return SmtUtils.quantifier(mMgdScript.getScript(), originalQuantifiedFormula.getQuantifier(),
				Arrays.asList(originalQuantifiedFormula.getVariables()), resultSubformula);
	}

	@Override
	protected boolean applyRepeatedlyUntilNoChange() {
		return SIMPLIFY_REPEATEDLY;
	}

	@Override
	protected void checkIntermediateResult(final Term context, final Term input, final Term output) {
		final LBool lBool = SmtUtils.checkEquivalenceUnderAssumption(input, output, context, mMgdScript.getScript());
		switch (lBool) {
		case SAT:
			throw new AssertionError(String.format(
					"Intermediate result not equivalent. Input: %s Output: %s Assumption: %s", input, output, context));
		case UNKNOWN:
			final ILogger logger = mServices.getLoggingService().getLogger(this.getClass());
			logger.info((String.format(
					"Insufficient ressources to check equivalence of intermediate result. Input: %s Output: %s Assumption: %s",
					input, output, context)));
			break;
		case UNSAT:
			break;
		default:
			throw new AssertionError("unknown value: " + lBool);
		}
	}

}
