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

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.DescendResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.TermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolyPoNeUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.Context;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.Context.CcTransformation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierOverapproximator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierOverapproximator.Quantifier;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
//import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SimplificationTest;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * @author Xinyu Jiang
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SimplifyDDA2 extends TermWalker<Term> {
	/**
	 * Replace terms of the form `x = l ∧ φ(x)` by `x = l ∧ φ(l)` and replace terms
	 * of the form `x ≠ l ∨ φ(x)` by `x ≠ l ∨ φ(l)`, where l is a literal (of sort
	 * Real, Int, or BitVec) and x is a variable in a {@link PolynomialRelation}
	 * (E.g., a {@link TermVariable}, a constant symbol (0-ary function symbol), a
	 * select term `(select a k)`.)
	 */
	private static final boolean APPLY_CONSTANT_FOLDING = false;
	private static final boolean DEBUG_CHECK_RESULT = false;
	private static final boolean USE_ECHO_COMMANDS = false;
	private static final boolean PREPROCESS_WITH_POLY_PAC_SIMPLIFICATION = true;
	private static final boolean DESCEND_INTO_QUANTIFIED_FORMULAS = true;
	/**
	 * This option allows us to omit quantified formulas from the critical
	 * constraint.
	 */
	private static final boolean OVERAPROXIMATE_QUANTIFIED_FORMULAS_IN_CONTEXT = true;
	private static final boolean SIMPLIFY_REPEATEDLY = true;
	private static final CheckedNodes CHECKED_NODES = CheckedNodes.ONLY_LEAVES;
	/**
	 * Do some overapproximation of quantifiers in the succedent of implications. We
	 * implement implication checks as satisfiability checks. If this variable is
	 * set to true, we overapproximate universally quantified formulas. (We keep
	 * existentially quantified formulas because SMT solver can handle them easily
	 * via Skolemization. <br>
	 * This option has no effect if check only leaves.
	 */
	private static final boolean OVERAPPROXIMATE_DIFFCULT_QUANTIFIERS_IN_NODES = false;
	/**
	 * Try to simplify modulo terms.
	 */
	private static final boolean MOD_SIMPLIFICATION = true;
	/**
	 * Try to apply a select-over-store simplification.
	 */
	private static final boolean ARRAY_SIMPLIFICATION = true;

	/**
	 * Options for which nodes to check for redundancy. To check redundancy, we
	 * check if the critical constraint at the current node implies either the
	 * formula at the node, or its negation. If a node is redundant, it will be
	 * replaces with `true` or `false`.
	 */
	private enum CheckedNodes {
		/**
		 * Only leaves checks only nodes that are considered leaves, including negated
		 * atoms. Quantified formulas are never considered as leaves.
		 */
		ONLY_LEAVES,
		/**
		 * All nodes checks every node for redundancy.
		 */
		ALL_NODES,
		/**
		 * Only leaves and quantified nodes treats quantified nodes as leaves.
		 */
		ONLY_LEAVES_AND_QUANTIFIED_NODES
	}

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	/**
	 * The assertion stack height keeps track of the number of pushes and pops we
	 * have made to the assertion stack of the SMT solver. It is cleared after each
	 * run/timeout, so that subsequent runs are not affected.
	 *
	 * We initialize it at 1, to make it possible for a user to input an initial
	 * critical constraint.
	 */
	private int mAssertionStackHeight = 1;
	private int mNumberOfCheckSatCommands = 0;
	private int mNonConstrainingNodes = 0;
	private int mNonRelaxingNodes = 0;
	private long mCheckSatTime = 0;
	private final long mStartTime = System.nanoTime();
	private final ArrayDeque<Map<TermVariable, Term>> mRenamingMaps;

	private SimplifyDDA2(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		super();
		mServices = services;
		mMgdScript = mgdScript;
		mRenamingMaps = new ArrayDeque<>();
	}

	@Override
	protected Term constructContextForApplicationTerm(final Term context, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam) {
		final List<Term> otherParams = DataStructureUtils.copyAllButOne(allParams, selectedParam);
		if (USE_ECHO_COMMANDS) {
			mMgdScript.lock(this);
			mMgdScript.echo(this, new QuotedObject("push in constructContextForApplicationTerm"));
			mMgdScript.unlock(this);
		}
		mMgdScript.getScript().push(1);
		mAssertionStackHeight++;

		final List<Term> newParams = new ArrayList<>();
		if (symb.getName().equals("and")) {
			for (final Term otherParam : otherParams) {
				final Term tmp;
				if (OVERAPROXIMATE_QUANTIFIED_FORMULAS_IN_CONTEXT) {
					// Replace universally quantified subformula by true.
					// We keep existentially quantified formulas, they are harmless and handled by
					// SMT solver via Skolemizations.
					tmp = replaceUniversalQuantifiersByTrue(mMgdScript, otherParam);
				} else {
					tmp = otherParam;
				}
				mMgdScript.getScript().assertTerm(tmp);
				newParams.add(tmp);
			}
		}

		if (symb.getName().equals("or")) {
			for (final Term otherParam : otherParams) {
				final Term tmp;
				if (OVERAPROXIMATE_QUANTIFIED_FORMULAS_IN_CONTEXT) {
					// As above we want to replace universally quantified subformulas by true.
					// Since we negate the otherParam, we replace instead existentially quantified
					// subformulas by false.
					tmp = replaceExistentialQuantifiersByFalse(mMgdScript, otherParam);
				} else {
					tmp = otherParam;
				}
				mMgdScript.getScript().assertTerm(SmtUtils.not(mMgdScript.getScript(), tmp));
				newParams.add(SmtUtils.not(mMgdScript.getScript(), tmp));
			}
		}
		return SmtUtils.and(mMgdScript.getScript(), newParams);
	}

	private Term replaceUniversalQuantifiersByTrue(final ManagedScript mgdScipt, final Term otherParam) {
		return QuantifierOverapproximator.apply(mgdScipt.getScript(), EnumSet.of(Quantifier.FORALL),
				mgdScipt.getScript().term("true"), otherParam);
	}

	private Term replaceExistentialQuantifiersByFalse(final ManagedScript mgdScipt, final Term otherParam) {
		return QuantifierOverapproximator.apply(mgdScipt.getScript(), EnumSet.of(Quantifier.EXISTS),
				mgdScipt.getScript().term("false"), otherParam);
	}

	@Override
	protected Term constructContextForQuantifiedFormula(final Term context, final int quant,
			final List<TermVariable> vars) {
		if (USE_ECHO_COMMANDS) {
			mMgdScript.lock(this);
			mMgdScript.echo(this, new QuotedObject("push in constructContextForQuantifiedFormula"));
			mMgdScript.unlock(this);
		}
		mMgdScript.getScript().push(1);
		mAssertionStackHeight++;
		return Context.buildCriticalContraintForQuantifiedFormula(mMgdScript.getScript(), context, vars,
				CcTransformation.TO_NNF);
	}

	/**
	 * Checks if the current node is a leaf, i.e., if we are at a atomic formula, or
	 * at a negated atomic formula. Additionally, quantified formulas are never
	 * considered to be leaves
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
	 * This method is called on subformulas, and checks if current the current
	 * subformula is redundant. A subformula is redundant if it can be replaced by
	 * true or false, and the resulting formula is logically equivalent to the
	 * original formula.
	 *
	 * We call a formula non-constraining if it can be replaced this way by true,
	 * and non-relaxing if it can be replaced by false.
	 *
	 * A subformula is non-constraining if it is implied by the critical constraint,
	 * and non-relaxing if it's negation is implied by the critical constraint.
	 *
	 * We assume that the critical constraint is asserted onto the assertion stack
	 * of the SMT solver.
	 */
	private DescendResult checkRedundancy(final Term term) {
		final Term result;
		{
			final long timeBeforeConstrainigcheck = System.nanoTime();
			mNumberOfCheckSatCommands++;
			final Term rhs;
			if (OVERAPPROXIMATE_DIFFCULT_QUANTIFIERS_IN_NODES) {
				rhs = replaceExistentialQuantifiersByFalse(mMgdScript, term);
			} else {
				rhs = term;
			}
			final LBool isNonConstraining = Util.checkSat(mMgdScript.getScript(),
					SmtUtils.not(mMgdScript.getScript(), rhs));
			mCheckSatTime += (System.nanoTime() - timeBeforeConstrainigcheck);
			if (isNonConstraining == LBool.UNSAT) {
				mNonConstrainingNodes++;
				result = mMgdScript.getScript().term("true");
				return new TermContextTransformationEngine.FinalResultForAscend(result);
			}
		}
		{
			mNumberOfCheckSatCommands++;
			final long timeBeforeRelaxingcheck = System.nanoTime();
			final Term rhs;
			if (OVERAPPROXIMATE_DIFFCULT_QUANTIFIERS_IN_NODES) {
				rhs = replaceUniversalQuantifiersByTrue(mMgdScript, term);
			} else {
				rhs = term;
			}
			final LBool isNonRelaxing = Util.checkSat(mMgdScript.getScript(), rhs);
			mCheckSatTime += (System.nanoTime() - timeBeforeRelaxingcheck);
			if (isNonRelaxing == LBool.UNSAT) {
				mNonRelaxingNodes++;
				result = mMgdScript.getScript().term("false");
				return new TermContextTransformationEngine.FinalResultForAscend(result);
			}
		}
		Term termBasedSimplification = term;
		if (MOD_SIMPLIFICATION) {
			final Term modSimplificationResult = tryModSimplification(term);
			if (modSimplificationResult != null) {
				termBasedSimplification = modSimplificationResult;
			}
		}
		if (ARRAY_SIMPLIFICATION) {
			final Term arraySimplificationResult = tryArraySimplification(termBasedSimplification);
			if (arraySimplificationResult != null) {
				termBasedSimplification = arraySimplificationResult;
			}
		}
		if (termBasedSimplification != term) {
			return new TermContextTransformationEngine.FinalResultForAscend(termBasedSimplification);
		}
		return null;
	}

	private Term tryModSimplification(final Term term) {
		final Predicate<Term> p = (x -> (x instanceof ApplicationTerm)
				&& ((ApplicationTerm) x).getFunction().getName().equals("mod"));
		final Set<Term> subTerms = SubTermFinder.find(term, p, true);
		if (subTerms.isEmpty()) {
			return null;
		}
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Term subTerm : subTerms) {
			ModTerm modTerm = ModTerm.of(subTerm);
			{
				// Check if we can apply the simplification recursively
				final Term divident = modTerm.getDivident();
				final Term tmp = tryModSimplification(divident);
				if (tmp != null) {
					modTerm = new ModTerm(tmp, modTerm.getDivisor());
				}
			}
			final Term dividentGeq0 = SmtUtils.geq(mMgdScript.getScript(), modTerm.getDivident(),
					SmtUtils.constructIntegerValue(mMgdScript.getScript(), SmtSortUtils.getIntSort(mMgdScript),
							BigInteger.ZERO));
			final Term dividentSmallerDivisor = SmtUtils.less(mMgdScript.getScript(), modTerm.getDivident(),
					modTerm.getDivisor());
			final Term inRange = SmtUtils.and(mMgdScript.getScript(), dividentGeq0, dividentSmallerDivisor);
			final Term notInRange = SmtUtils.not(mMgdScript.getScript(), inRange);
			final LBool modIsSuperfluous = Util.checkSat(mMgdScript.getScript(), notInRange);
			if (modIsSuperfluous == LBool.UNSAT) {
				substitutionMapping.put(subTerm, modTerm.getDivident());
			}
		}
		if (!substitutionMapping.isEmpty()) {
			return Substitution.apply(mMgdScript, substitutionMapping, term);
		} else {
			return null;
		}
	}

	private Term tryArraySimplification(final Term term) {
		final List<MultiDimensionalSelectOverNestedStore> list = MultiDimensionalSelectOverNestedStore
				.extractMultiDimensionalSelectOverNestedStore(term, true);
		if (list.isEmpty()) {
			return null;
		}
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final MultiDimensionalSelectOverNestedStore mdsons : list) {
			if (mdsons.getNestedStore().getValues().size() != 1) {
				continue;
			}
			final ArrayIndex storeIndex = mdsons.getNestedStore().getIndices().get(0);
			final ArrayIndex selectIndex = mdsons.getSelectIndex();
			final Term idxEquivalence = ArrayIndex.constructIndexEquality(mMgdScript.getScript(), storeIndex,
					selectIndex);
			final LBool idxEquivalent = Util.checkSat(mMgdScript.getScript(),
					SmtUtils.not(mMgdScript.getScript(), idxEquivalence));
			if (idxEquivalent == LBool.UNSAT) {
				substitutionMapping.put(mdsons.toTerm(mMgdScript.getScript()),
						mdsons.getNestedStore().getValues().get(0));
				continue;
			}
			final LBool idxNotEquivalent = Util.checkSat(mMgdScript.getScript(), idxEquivalence);
			if (idxNotEquivalent == LBool.UNSAT) {
				final MultiDimensionalSelect mds = new MultiDimensionalSelect(mdsons.getNestedStore().getArray(),
						mdsons.getSelectIndex());
				substitutionMapping.put(mdsons.toTerm(mMgdScript.getScript()), mds.toTerm(mMgdScript.getScript()));
			}
		}
		if (!substitutionMapping.isEmpty()) {
			return Substitution.apply(mMgdScript, substitutionMapping, term);
		} else {
			return null;
		}
	}

	/**
	 * Constructs a fresh constant symbol for each bound quantified variable.
	 */
	private QuantifiedFormula preprocessQuantifiedFormula(final QuantifiedFormula term, final Term context) {
		mMgdScript.lock(this);
		final Map<TermVariable, Term> substitutionMapping = constructFreshConstantSymbols(mMgdScript,
				Arrays.asList(term.getVariables()), term, context);
		mRenamingMaps.push(substitutionMapping);
		mMgdScript.unlock(this);
		final Term substitutedSubformula = Substitution.apply(mMgdScript, substitutionMapping, term.getSubformula());
		return (QuantifiedFormula) mMgdScript.getScript().quantifier(term.getQuantifier(), term.getVariables(),
				substitutedSubformula);
	}

	/**
	 * Given a collection of {@link TermVariable}s, construct a fresh constant
	 * symbol for each {@link TermVariable} and return a map that maps each
	 * {@link TermVariable} to its fresh constant symbol.
	 */
	private static Map<TermVariable, Term> constructFreshConstantSymbols(final ManagedScript mgdScript,
			final Collection<TermVariable> tvs, final Term term, final Term context) {
		final Map<TermVariable, Term> result = new HashMap<>();
		for (final TermVariable tv : tvs) {
			final Term constantSymbol = constructFreshConstantSymbol(mgdScript, tv, term, context);
			result.put(tv, constantSymbol);
		}
		return result;
	}

	/**
	 * Construct a constant symbol (reminder constant symbol is a 0-ary
	 * {@link ApplicationTerm}). The constant symbol should be fresh (i.e.,
	 * different from all constant symbols that have been declared already.
	 * Unfortunately, we do not have a reliable mechanism for getting fresh constant
	 * symbols. As a workaround we add a suffix to the variable name and hope that
	 * this name did not yet occur. If the name did already occur the {@link Script}
	 * will throw and {@link SMTLIBException}. We expect that this will never happen
	 * in practice and hence do not handle this exception.
	 */
	private static Term constructFreshConstantSymbol(final ManagedScript mgdScript, final TermVariable tv,
			final Term term, final Term context) {
		final String name = tv.getName() + "_SimplifyDDA_" + tv.hashCode() + "_" + term.hashCode() + "_"
				+ context.hashCode();
		mgdScript.getScript().declareFun(name, new Sort[0], tv.getSort());
		return mgdScript.getScript().term(name);
	}

	/**
	 * Boolean for determining whether we check the redundancy of a node given the
	 * initial flag settings.
	 */
	private static boolean checkRedundancyForNode(final Term term) {
		return ((CHECKED_NODES == CheckedNodes.ALL_NODES)
				|| ((CHECKED_NODES == CheckedNodes.ONLY_LEAVES_AND_QUANTIFIED_NODES)
						&& (term instanceof QuantifiedFormula || isLeaf(term)))
				|| (CHECKED_NODES == CheckedNodes.ONLY_LEAVES && isLeaf(term)));
	}

	private Term doConstantFolding(final Term context, final Term term) {
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
			return renamed;
		}
		return term;
	}

	/**
	 * Simplifies the formula based on if we want to preprocess it with PolyPac
	 * simplification or constant folding. Constant folding is already applied in
	 * the PolyPac simplification.
	 */
	@Override
	protected DescendResult convert(final Term context, final Term term) {
		Term preprocessedTerm = term;
		if (PREPROCESS_WITH_POLY_PAC_SIMPLIFICATION) {
			if (APPLY_CONSTANT_FOLDING) {
				throw new AssertionError("PolyPac Simplefication Already Implements Constant Folding");
			}
			preprocessedTerm = PolyPacSimplificationTermWalker.simplify(mServices, mMgdScript, context, term);
		} else if (APPLY_CONSTANT_FOLDING) {
			preprocessedTerm = doConstantFolding(context, term);
		} else {
			preprocessedTerm = term;
		}
		return convertForPreprocessedInputTerms(context, preprocessedTerm);
	}

	/**
	 * Checks if we want to attempt to simplify the current node, and returns an
	 * ascend or descend result accordingly. If we descend into a quantified
	 * formula, it is first preprocessed.,
	 */
	private DescendResult convertForPreprocessedInputTerms(final Term context, final Term term) {

		if (SmtUtils.isFalseLiteral(context)) {
			throw new AssertionError("critical constraint is false");
		}
		DescendResult result;
		final boolean descend = (DESCEND_INTO_QUANTIFIED_FORMULAS && term instanceof QuantifiedFormula)
				|| !(isLeaf(term) || term instanceof QuantifiedFormula);
		if (checkRedundancyForNode(term) && ((result = checkRedundancy(term)) != null)) {
			if (USE_ECHO_COMMANDS) {
				mMgdScript.lock(this);
				mMgdScript.echo(this, new QuotedObject("pop in convert, node is redundant"));
				mMgdScript.unlock(this);
			}
			mMgdScript.getScript().pop(1);
			mAssertionStackHeight--;
			return result;
		} else if (descend) {
			if (term instanceof QuantifiedFormula) {
				return new TermContextTransformationEngine.IntermediateResultForDescend(
						preprocessQuantifiedFormula((QuantifiedFormula) term, context));
			} else {
				return new TermContextTransformationEngine.IntermediateResultForDescend(term);
			}
		} else {
			if (USE_ECHO_COMMANDS) {
				mMgdScript.lock(this);
				mMgdScript.echo(this, new QuotedObject("pop in convert, not redundant and not descend"));
				mMgdScript.unlock(this);
			}
			mMgdScript.getScript().pop(1);
			mAssertionStackHeight--;
			return new TermContextTransformationEngine.FinalResultForAscend(term);
		}
	}

	@Override
	protected Term constructResultForApplicationTerm(final Term context, final ApplicationTerm originalApplicationTerm,
			final Term[] resultParams) {
		if (USE_ECHO_COMMANDS) {
			mMgdScript.lock(this);
			mMgdScript.echo(this, new QuotedObject("pop in constructResultForApplicationTerm"));
			mMgdScript.unlock(this);
		}
		mMgdScript.getScript().pop(1);
		mAssertionStackHeight--;

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
		if (SmtUtils.isFalseLiteral(context)) {
			// Handle this special case immediately. If the context is `false`, the
			// simplification may return any term, we choose false.
			// We want to handle this special case here since the later algorithm has the
			// invariant that the context is never `false`. (Probably this is only an
			// invariant under certain assumption that have to be determined.)
			return context;
		}
		final SimplifyDDA2 simplifyDDA2 = new SimplifyDDA2(services, mgdScript);
		// do initial push
		mgdScript.getScript().push(1);
		final Set<TermVariable> freeVariables = new HashSet<>();
		freeVariables.addAll(Arrays.asList(context.getFreeVars()));
		freeVariables.addAll(Arrays.asList(term.getFreeVars()));
		final Map<TermVariable, Term> substitutionMapping = constructFreshConstantSymbols(mgdScript, freeVariables,
				term, context);
		final Term closedContext = Substitution.apply(mgdScript, substitutionMapping, context);
		final Term closedTerm = Substitution.apply(mgdScript, substitutionMapping, term);
		mgdScript.getScript().assertTerm(closedContext);
		final Term result;
		try {
			final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(closedTerm);
			final Comparator<Term> siblingOrder = new TreeSizeComperator(CommuhashUtils.HASH_BASED_COMPERATOR);
			final Term intermediateResult = TermContextTransformationEngine.transform(simplifyDDA2, siblingOrder,
					closedContext, nnf);
			if (substitutionMapping.isEmpty()) {
				result = intermediateResult;
			} else {
				final Map<Term, TermVariable> reversedSubstitutionMapping = reverseMap(substitutionMapping);
				result = Substitution.apply(mgdScript, reversedSubstitutionMapping, intermediateResult);
			}
			final ILogger logger = services.getLoggingService().getLogger(SimplifyDDA2.class);
			if (logger.isDebugEnabled()) {
				logger.debug(simplifyDDA2.generateExitMessage());
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
		} finally {
			if (mgdScript.isLocked()) {
				throw new AssertionError("ManagedScript is still locked");
			}
		}
		return result;
	}

	public int getAssertionStackHeight() {
		return mAssertionStackHeight;
	}

	public void clearStack() {
		while (mAssertionStackHeight > 0) {
			if (USE_ECHO_COMMANDS) {
				mMgdScript.lock(this);
				mMgdScript.echo(this, new QuotedObject("pop for clearStack"));
				mMgdScript.unlock(this);
			}
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
		final Map<TermVariable, Term> orginalTvsToFreshConstants = mRenamingMaps.pop();
		final Map<Term, TermVariable> reverseMap = reverseMap(orginalTvsToFreshConstants);
		final Term subformulaWithOriginalVariables = Substitution.apply(mMgdScript, reverseMap, resultSubformula);
		if (USE_ECHO_COMMANDS) {
			mMgdScript.lock(this);
			mMgdScript.echo(this, new QuotedObject("pop in constructResultForQuantifiedFormula"));
			mMgdScript.unlock(this);
		}
		mMgdScript.getScript().pop(1);
		mAssertionStackHeight--;
		assert mAssertionStackHeight >= 0;
		return SmtUtils.quantifier(mMgdScript.getScript(), originalQuantifiedFormula.getQuantifier(),
				orginalTvsToFreshConstants.keySet(), subformulaWithOriginalVariables);
	}

	private static <A, B> Map<B, A> reverseMap(final Map<A, B> map) {
		final Map<B, A> reverseMap = new HashMap<>();
		for (final Map.Entry<A, B> entry : map.entrySet()) {
			reverseMap.put(entry.getValue(), entry.getKey());
		}
		return reverseMap;
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
