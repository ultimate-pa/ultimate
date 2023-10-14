/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol.BvSignedness;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.CnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm.Equivalence;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStore3;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStorePlain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.simplify.SimplifyDDAWithTimeout;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.simplify.SimplifyQuick;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de) (methods added by me are marked specifically)
 */
public final class SmtUtils {

	private static final String[] EMPTY_INDICES = new String[0];
	private static final BigInteger[] EMPTY_INDICES_BI = new BigInteger[0];

	private static final String ERROR_MESSAGE_UNKNOWN_ENUM_CONSTANT = "unknown enum constant ";
	private static final String ERROR_MSG_UNKNOWN_SORT = "unknown sort ";
	/**
	 * Avoid the construction of "bvadd" with more than two arguments and use nested "bvadd" terms instead.
	 */
	private static final boolean BINARY_BITVECTOR_SUM_WORKAROUND = false;

	/**
	 * Name of a non-standard FloatingPoint extension that is supported by Z3.
	 */
	public static final String FP_TO_IEEE_BV_EXTENSION = "fp.to_ieee_bv";


	/**
	 * Enum for conjunctions and disjunctions. The toString method returns the
	 * string that is required to construct a term via {@link Script#term} or
	 * {@link SmtUtils#unfTerm}
	 *
	 */
	public enum Junction {
		AND {
			@Override
			public String toString() {
				return "and";
			}
		},
		OR {
			@Override
			public String toString() {
				return "or";
			}
		}
	}

	public enum XnfConversionTechnique {
		BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION
	}

	public enum SimplificationTechnique {
		SIMPLIFY_QUICK(true),

		SIMPLIFY_DDA(true),

		SIMPLIFY_DDA2(true),

		POLY_PAC(false),

		/**
		 * Simplification that uses the (non-standard) simplify command which is
		 * implemented by some SMT solvers.
		 */
		NATIVE(false),

		NONE(false);

		private final boolean mDetectsUnsatisfiability;

		SimplificationTechnique(final boolean decidesFeasibility) {
			mDetectsUnsatisfiability = decidesFeasibility;
		}

		/**
		 * @return true iff this unsatisfiable formulas are simplified to `false`
		 */
		public boolean detectsUnsatisfiability() {
			return mDetectsUnsatisfiability;
		}
	}

	private static final boolean EXTENDED_LOCAL_SIMPLIFICATION = true;

	/**
	 * Has problems with {@link ElimStore3}. Set to true once {@link ElimStore3} has been replace by
	 * {@link ElimStorePlain}.
	 */
	private static final boolean FLATTEN_ARRAY_TERMS = true;
	private static final boolean DEBUG_ASSERT_ULTIMATE_NORMAL_FORM = false;
	private static final boolean DEBUG_CHECK_EVERY_SIMPLIFICATION = false;

	private SmtUtils() {
		// Prevent instantiation of this utility class
	}

	public static Term simplify(final ManagedScript mgdScript, final Term formula,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique) {
		return simplify(mgdScript, formula, mgdScript.getScript().term("true"), services, simplificationTechnique);
	}

	public static Term simplify(final ManagedScript mgdScript, final Term formula, final Term context,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique) {
		if (simplificationTechnique == SimplificationTechnique.NONE) {
			return formula;
		}
		mgdScript.assertScriptNotLocked();
		Objects.requireNonNull(context);
		final ILogger logger = services.getLoggingService().getLogger(SmtLibUtils.PLUGIN_ID);
		if (logger.isDebugEnabled()) {
			logger.debug(new DebugMessage("simplifying formula of DAG size {0}", new DagSizePrinter(formula)));
		}
		if (!SmtUtils.isTrueLiteral(context) && simplificationTechnique != SimplificationTechnique.POLY_PAC
				&& simplificationTechnique != SimplificationTechnique.SIMPLIFY_DDA
				&& simplificationTechnique != SimplificationTechnique.SIMPLIFY_DDA2
				&& simplificationTechnique != SimplificationTechnique.NATIVE
				&& simplificationTechnique != SimplificationTechnique.NONE) {
			throw new UnsupportedOperationException(
					simplificationTechnique + " does not support simplification with respect to context");
		}
		final long startTime = System.nanoTime();
		final UndoableWrapperScript undoableScript = new UndoableWrapperScript(mgdScript.getScript());
		final ManagedScript script = new ManagedScript(services, undoableScript);
		try {
			final Term simplified;
			switch (simplificationTechnique) {
			case SIMPLIFY_DDA:
				simplified = new SimplifyDDAWithTimeout(script.getScript(), true, services, context)
						.getSimplifiedTerm(formula);
				break;
			case SIMPLIFY_DDA2:
				simplified = SimplifyDDA2.simplify(services, script, context, formula);
				break;
			case SIMPLIFY_QUICK:
				simplified = new SimplifyQuick(script.getScript(), services).getSimplifiedTerm(formula);
				break;
			case NONE:
				return formula;
			case POLY_PAC:
				simplified = PolyPacSimplificationTermWalker.simplify(services, script, context, formula);
				break;
			case NATIVE:
				script.getScript().push(1);
				script.getScript().assertTerm(context);
				simplified = script.getScript().simplify(formula);
				script.getScript().pop(1);
				break;
			default:
				throw new AssertionError(ERROR_MESSAGE_UNKNOWN_ENUM_CONSTANT + simplificationTechnique);
			}
			if (logger.isDebugEnabled()) {
				logger.debug(new DebugMessage("DAG size before simplification {0}, DAG size after simplification {1}",
						new DagSizePrinter(formula), new DagSizePrinter(simplified)));
			}
			final long endTime = System.nanoTime();
			final long overallTimeMs = (endTime - startTime) / 1_000_000;
			// write warning if simplification takes more than 5 seconds
			if (overallTimeMs >= 5000) {
				final StringBuilder sb = new StringBuilder();
				sb.append("Spent ").append(CoreUtil.humanReadableTime(overallTimeMs, TimeUnit.MILLISECONDS, 2))
						.append(" on a formula simplification");
				if (formula.equals(simplified)) {
					sb.append(" that was a NOOP. DAG size: ");
					sb.append(new DagSizePrinter(formula));
				} else {
					sb.append(". DAG size of input: ");
					sb.append(new DagSizePrinter(formula));
					sb.append(" DAG size of output: ");
					sb.append(new DagSizePrinter(simplified));
				}
				sb.append(" (called from ").append(ReflectionUtil.getCallerSignatureFiltered(Set.of(SmtUtils.class)))
						.append(")");
				logger.warn(sb);
				// Matthias 2023-08-01: The following is a hack for writing simplification
				// benchmarks to a file. We write only if the simplification took at least 5s
				// (see if above) and if the context is equivalent to true.
				final boolean writeSimplificationBenchmarksToFile = false;
				if (writeSimplificationBenchmarksToFile && SmtUtils.isTrueLiteral(context)) {
					try (FileWriter fw = new FileWriter("SimplificationBenchmark_" + overallTimeMs);
							BufferedWriter bw = new BufferedWriter(fw);
							PrintWriter out = new PrintWriter(bw)) {
						out.println(SmtTestGenerationUtils.generateStringForTestfile(formula));
						out.close();
						bw.close();
						fw.close();
					} catch (final IOException e) {
						throw new AssertionError(e);
					}
				}
			}
			// TODO: DD 2019-11-19: This call is a dirty hack! SimplifyDDAWithTimeout leaves an empty stack frame open,
			// but I do not want to try and debug how it is happening.
			undoableScript.restore();
			if (simplified != formula) {
				// TODO: Matthias 2019-11-19 SimplifyDDA can produce nested
				// conjunctions or disjunctions. Use UnfTransformer to get
				// rid of these.
				return new UnfTransformer(script.getScript()).transform(simplified);
			}
			return simplified;
		} catch (final ToolchainCanceledException t) {
			// we try to preserve the script if a timeout occurred
			final int dirtyLevels = undoableScript.restore();
			if (dirtyLevels > 0) {
				logger.warn("Removed " + dirtyLevels + " from assertion stack");
			}
			throw t;
		}
	}

	public static ExtendedSimplificationResult simplifyWithStatistics(final ManagedScript mgdScript, final Term formula,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique) {
		return simplifyWithStatistics(mgdScript, formula, mgdScript.term(null, "true"), services, simplificationTechnique);
	}

	public static ExtendedSimplificationResult simplifyWithStatistics(final ManagedScript mgdScript, final Term formula,
			final Term context, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		final long startTime = System.nanoTime();
		final long sizeBefore = new DAGSize().treesize(formula);
		final Term simplified = simplify(mgdScript, formula, context, services, simplificationTechnique);
		final long sizeAfter = new DAGSize().treesize(simplified);
		final long endTime = System.nanoTime();
		return new ExtendedSimplificationResult(simplified, endTime - startTime, sizeBefore - sizeAfter,
				(double) sizeAfter / sizeBefore * 100);
	}

	public static LBool checkSatTerm(final Script script, final Term formula) {
		return Util.checkSat(script, formula);
	}

	/**
	 * If term is a conjunction return all conjuncts, otherwise return term.
	 */
	public static Term[] getConjuncts(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if ("and".equals(appTerm.getFunction().getName())) {
				return appTerm.getParameters();
			}
		}
		final Term[] result = new Term[1];
		result[0] = term;
		return result;
	}

	/**
	 * Converts a term in CNF and produces an array of conjuncts.
	 *
	 * @param mgnScript
	 * @param services
	 * @param splitNumericEqualities
	 *            iff true, numeric equality relations (e.g., (= x 3)) are converted to inequalities (e.g., (and (>= x
	 *            3) (<= x 3)).
	 * @param term
	 *            The term that should be cannibalized
	 * @return
	 */
	public static Term[] cannibalize(final ManagedScript mgnScript, final IUltimateServiceProvider services,
			final boolean splitNumericEqualities, final Term term) {
		final Term cnf = new CnfTransformer(mgnScript, services).transform(term);
		if (splitNumericEqualities) {
			return splitNumericEqualities(mgnScript.getScript(), SmtUtils.getConjuncts(cnf));
		}
		return SmtUtils.getConjuncts(cnf);
	}

	private static Term[] splitNumericEqualities(final Script script, final Term[] conjuncts) {
		final ArrayList<Term> result = new ArrayList<>(conjuncts.length * 2);
		for (final Term conjunct : conjuncts) {
			final BinaryNumericRelation bnr = BinaryNumericRelation.convert(conjunct);
			if (bnr == null) {
				result.add(conjunct);
			} else if (bnr.getRelationSymbol() == RelationSymbol.EQ) {
				final Term leq = script.term("<=", bnr.getLhs(), bnr.getRhs());
				result.add(leq);
				final Term geq = script.term(">=", bnr.getLhs(), bnr.getRhs());
				result.add(geq);
			} else {
				result.add(conjunct);
			}
		}
		return result.toArray(new Term[result.size()]);
	}

	/**
	 * If term is a disjunction return all disjuncts, otherwise return term.
	 */
	public static Term[] getDisjuncts(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if ("or".equals(appTerm.getFunction().getName())) {
				return appTerm.getParameters();
			}
		}
		final Term[] result = new Term[1];
		result[0] = term;
		return result;
	}

	/**
	 * Takes an ApplicationTerm with pairwise function symbol (e.g. distinct) or chainable function symbol (e.g.
	 * equality) and return a conjunction of pairwise applications of the function symbol. E.g. the ternary equality (=
	 * a b c) becomes (and (= a b) (= a c) (= b c)).
	 */
	public static Term binarize(final Script script, final ApplicationTerm term) {
		final FunctionSymbol functionSymbol = term.getFunction();
		if (!functionSymbol.isPairwise() && !functionSymbol.isChainable()) {
			throw new IllegalArgumentException("can only binarize pairwise terms");
		}
		final String functionName = functionSymbol.getApplicationString();
		final Term[] params = term.getParameters();
		assert params.length > 1;
		final List<Term> conjuncts = new ArrayList<>();
		for (int i = 0; i < params.length; i++) {
			for (int j = i + 1; j < params.length; j++) {
				conjuncts.add(script.term(functionName, params[i], params[j]));
			}
		}
		return SmtUtils.and(script, conjuncts.toArray(new Term[conjuncts.size()]));
	}

	public static boolean firstParamIsBool(final ApplicationTerm term) {
		final Term[] params = term.getParameters();
		return SmtSortUtils.isBoolSort(params[0].getSort());
	}

	public static boolean allParamsAreBool(final ApplicationTerm term) {
		return Arrays.stream(term.getParameters()).map(Term::getSort).allMatch(SmtSortUtils::isBoolSort);
	}

	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is equivalent to (= lhs rhs) but uses only the
	 * boolean connectives "and" and "or".
	 */
	public static Term binaryBooleanEquality(final Script script, final Term lhs, final Term rhs) {
		assert SmtSortUtils.isBoolSort(lhs.getSort());
		assert SmtSortUtils.isBoolSort(rhs.getSort());
		final Term bothTrue = SmtUtils.and(script, lhs, rhs);
		final Term bothFalse = SmtUtils.and(script, SmtUtils.not(script, lhs), SmtUtils.not(script, rhs));
		return SmtUtils.or(script, bothTrue, bothFalse);
	}

	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is equivalent to (not (= lhs rhs)) but uses only
	 * the boolean connectives "and" and "or".
	 */
	public static Term binaryBooleanNotEquals(final Script script, final Term lhs, final Term rhs) {
		assert SmtSortUtils.isBoolSort(lhs.getSort());
		assert SmtSortUtils.isBoolSort(rhs.getSort());
		final Term oneIsTrue = SmtUtils.or(script, lhs, rhs);
		final Term oneIsFalse = SmtUtils.or(script, SmtUtils.not(script, lhs), SmtUtils.not(script, rhs));
		return SmtUtils.and(script, oneIsTrue, oneIsFalse);
	}

	/**
	 * Given a list of Terms term1, ... ,termn returns a new list that contains (not term1), ... ,(not termn) in this
	 * order.
	 */
	public static List<Term> negateElementwise(final Script script, final List<Term> terms) {
		final List<Term> result = new ArrayList<>(terms.size());
		for (final Term term : terms) {
			result.add(SmtUtils.not(script, term));
		}
		return result;
	}

	/**
	 * Returns the term that selects the element at index from (possibly) multi dimensional array a. E.g. If the array
	 * has Sort (Int -> Int -> Int) and index is [23, 42], this method returns the term ("select" ("select" a 23) 42).
	 */
	public static Term multiDimensionalSelect(final Script script, final Term a, final ArrayIndex index) {
		assert a.getSort().isArraySort();
		Term result = a;
		for (int i = 0; i < index.size(); i++) {
			result = SmtUtils.select(script, result, index.get(i));
		}
		return result;
	}

	/**
	 * Returns the term that stores the element at index from (possibly) multi dimensional array a. E.g. If the array
	 * has Sort (Int -> Int -> Int) and we store the value val at index [23, 42], this method returns the term (store a
	 * 23 (store (select a 23) 42 val)).
	 */
	public static Term multiDimensionalStore(final Script script, final Term a, final ArrayIndex index,
			final Term value) {
		assert !index.isEmpty();
		assert a.getSort().isArraySort();
		Term result = value;
		for (int i = index.size() - 1; i >= 0; i--) {
			final Term selectUpToI = multiDimensionalSelect(script, a, index.getFirst(i));
			result = SmtUtils.store(script, selectUpToI, index.get(i), result);
		}
		return result;
	}

	/**
	 * Returns true iff each key and each value is non-null.
	 */
	public static <K, V> boolean neitherKeyNorValueIsNull(final Map<K, V> map) {
		for (final Entry<K, V> entry : map.entrySet()) {
			if (entry.getKey() == null || entry.getValue() == null) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Given the array of terms [lhs_1, ..., lhs_n] and the array of terms [rhs_1, ..., rhs_n], return the conjunction
	 * of the following equalities lhs_1 = rhs_1, ... , lhs_n = rhs_n.
	 */
	public static Term pairwiseEquality(final Script script, final List<? extends Term> lhs,
			final List<? extends Term> rhs) {
		if (lhs.size() != rhs.size()) {
			throw new IllegalArgumentException("must have same length");
		}
		final Term[] equalities = new Term[lhs.size()];
		for (int i = 0; i < lhs.size(); i++) {
			equalities[i] = binaryEquality(script, lhs.get(i), rhs.get(i));
		}
		return SmtUtils.and(script, equalities);
	}

	/**
	 * Construct the following term. (index1 == index2) ==> (value1 == value2)
	 */
	public static Term indexEqualityImpliesValueEquality(final Script script, final ArrayIndex index1,
			final ArrayIndex index2, final Term value1, final Term value2) {
		assert index1.size() == index2.size();
		final Term lhs = pairwiseEquality(script, index1, index2);
		final Term rhs = binaryEquality(script, value1, value2);
		return SmtUtils.or(script, not(script, lhs), rhs);
	}

	/**
	 * Return term that represents the sum of all summands. Return the neutral element for sort sort if summands is
	 * empty. (This method should be kept simple and does not remove "0" from the list of summands. If you want to get
	 * rid of "0" then use {@link AffineTerm}).
	 */
	public static Term sum(final Script script, final Sort sort, final Term... summands) {
		assert SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBitvecSort(sort);
		if (summands.length == 0) {

			if (SmtSortUtils.isIntSort(sort) || SmtSortUtils.isRealSort(sort)) {
				return Rational.ZERO.toTerm(sort);
			}
			if (SmtSortUtils.isBitvecSort(sort)) {
				return BitvectorUtils.constructTerm(script, BigInteger.ZERO, sort);
			}
			throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
		}
		if (summands.length == 1) {
			return summands[0];
		}
		if (SmtSortUtils.isNumericSort(sort)) {
			return script.term("+", CommuhashUtils.sortByHashCode(summands));
		}
		if (!SmtSortUtils.isBitvecSort(sort)) {
			throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
		}
		if (BINARY_BITVECTOR_SUM_WORKAROUND) {
			return binaryBitvectorSum(script, sort, summands);
		}
		return script.term("bvadd", CommuhashUtils.sortByHashCode(summands));
	}

	/**
	 * Construct nested binary "bvadd" terms.
	 *
	 * @param sort
	 *            bitvector sort of the arguments (required if summands is empty)
	 * @param summands
	 *            bitvector terms that each have the same sort
	 */
	public static Term binaryBitvectorSum(final Script script, final Sort sort, final Term... summands) {
		if (summands.length == 0) {
			return BitvectorUtils.constructTerm(script, BigInteger.ZERO, sort);
		}
		if (summands.length == 1) {
			return summands[0];
		}
		Term result = script.term("bvadd", summands[0], summands[1]);
		for (int i = 2; i < summands.length; i++) {
			result = script.term("bvadd", result, summands[i]);
		}
		return result;
	}

	public static Term mul(final Script script, final Rational rational, final Term term) {
		if (rational.equals(Rational.ONE)) {
			return term;
		}
		if (rational.equals(Rational.MONE)) {
			return SmtUtils.neg(script, term);
		}
		final Term coefficient = SmtUtils.rational2Term(script, rational, term.getSort());
		return SmtUtils.mul(script, term.getSort(), coefficient, term);
	}

	/**
	 * Return term that represents the product of all factors. Return the neutral element for sort sort if factors is
	 * empty.
	 */
	public static Term mul(final Script script, final Sort sort, final Term... factors) {
		assert SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBitvecSort(sort);
		if (factors.length == 0) {
			final BigInteger one = BigInteger.ONE;
			return constructIntegerValue(script, sort, one);
		}
		if (factors.length == 1) {
			return factors[0];
		}
		if (SmtSortUtils.isNumericSort(sort)) {
			return script.term("*", CommuhashUtils.sortByHashCode(factors));
		}
		if (SmtSortUtils.isBitvecSort(sort)) {
			return script.term("bvmul", CommuhashUtils.sortByHashCode(factors));
		}
		throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
	}

	/**
	 * Return sum, in affine representation if possible.
	 *
	 * @param funcname
	 *            either "+" or "bvadd".
	 */
	public static Term sum(final Script script, final String funcname, final Term... summands) {
		assert "+".equals(funcname) || "bvadd".equals(funcname);
		final Term sum = script.term(funcname, summands);
		final AffineTerm affine = (AffineTerm) new AffineTermTransformer(script).transform(sum);
		if (affine.isErrorTerm()) {
			return sum;
		}
		return affine.toTerm(script);
	}

	/**
	 * Return product, in affine representation if possible.
	 *
	 * @param funcname
	 *            either "*" or "bvmul".
	 */
	public static Term mul(final Script script, final String funcname, final Term... factors) {
		assert "*".equals(funcname) || "bvmul".equals(funcname);
		final Term product;
		if (factors.length == 0) {
			throw new UnsupportedOperationException("Method does not support empty factors.");
		}
		if (factors.length == 1) {
			product = factors[0];
		} else {
			product = script.term(funcname, CommuhashUtils.sortByHashCode(factors));
		}
		final AffineTerm affine = (AffineTerm) new AffineTermTransformer(script).transform(product);
		if (affine.isErrorTerm()) {
			return product;
		}
		return affine.toTerm(script);
	}

	public static Term minus(final Script script, final Term... operands) {
		if (operands.length <= 1) {
			throw new UnsupportedOperationException("use neg for unary minus");
		}
		final Term[] newOperands = new Term[operands.length];
		newOperands[0] = operands[0];
		for (int i = 1; i < operands.length; i++) {
			newOperands[i] = neg(script, operands[i]);
		}
		String funcname;
		final Sort sort = operands[0].getSort();
		if (SmtSortUtils.isNumericSort(sort)) {
			funcname = "+";
		} else if (SmtSortUtils.isBitvecSort(sort)) {
			funcname = "bvadd";
		} else {
			throw new UnsupportedOperationException("unsupported sort " + sort);
		}
		return sum(script, funcname, newOperands);

	}

	/**
	 * Return term that represents negation (unary minus).
	 */
	public static Term neg(final Script script, final Term operand) {
		final Sort sort = operand.getSort();
		assert SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBitvecSort(sort);
		if (SmtSortUtils.isNumericSort(sort)) {
			return unaryNumericMinus(script, operand);
		}
		if (SmtSortUtils.isBitvecSort(sort)) {
			return BitvectorUtils.unfTerm(script, "bvneg", null, operand);
		}
		throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
	}

	public static Term unaryNumericMinus(final Script script, final Term operand) {
		if (operand instanceof ConstantTerm) {
			final ConstantTerm ct = (ConstantTerm) operand;
			final Rational value = toRational(ct);
			return value.negate().toTerm(operand.getSort());
		}
		if (operand instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) operand;
			if (appTerm.getFunction().isIntern()) {
				if (isUnaryNumericMinus(appTerm.getFunction())) {
					return appTerm.getParameters()[0];
				}
				if (appTerm.getFunction().getName().equals("+")) {
					return sum(script, operand.getSort(), Arrays.stream(appTerm.getParameters())
							.map(x -> unaryNumericMinus(script, x)).toArray(Term[]::new));
				}
				// TODO: handle all theory-defined functions
				return script.term("-", operand);
			}
			return script.term("-", operand);
		}
		if (operand instanceof TermVariable) {
			return script.term("-", operand);
		}
		throw new UnsupportedOperationException("cannot apply unary minus to " + operand.getClass().getSimpleName());
	}

	/**
	 * Return term that represents negation of boolean term.
	 */
	public static Term not(final Script script, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getParameters().length == 2) {
				final String funcName = appTerm.getFunction().getName();
				if (funcName.equals("distinct") && appTerm.getParameters().length == 2) {
					return SmtUtils.binaryEquality(script, appTerm.getParameters()[0], appTerm.getParameters()[1]);
				}
				if (funcName.equals("<") || funcName.equals("<=") || funcName.equals(">") || funcName.equals(">=")) {
					final PolynomialRelation polyRel = PolynomialRelation.of(script, term);
					return polyRel.negate().toTerm(script);
				}
			}
			return Util.not(script, term);
		}
		return Util.not(script, term);
	}

	/**
	 * Return term that represents (or (not lhs) rhs).
	 */
	public static Term implies(final Script script, final Term lhs, final Term rhs) {
		return or(script, not(script, lhs), rhs);
	}

	/**
	 * TODO 20210516 Matthias: Extend optimizations of the methods called by {@link SmtUtils#binaryEquality} to this
	 * method. Currently, this is not very important since we have mainly binary equalities in program verification.
	 *
	 */
	public static Term equality(final Script script, final Term... params) {
		if (params.length == 2) {
			return binaryEquality(script, params[0], params[1]);
		}
		return script.term("=", CommuhashUtils.sortByHashCode(params));
	}

	/**
	 * Returns the equality ("=" lhs rhs), or true resp. false if some simple checks detect validity or unsatisfiablity
	 * of the equality.
	 */
	public static Term binaryEquality(final Script script, final Term lhs, final Term rhs) {
		if (lhs == rhs) {
			return script.term("true");
		}
		if (lhs.getSort().isNumericSort()) {
			return numericEquality(script, lhs, rhs);
		}
		if (SmtSortUtils.isBoolSort(lhs.getSort())) {
			return booleanEquality(script, lhs, rhs);
		}
		if (SmtSortUtils.isBitvecSort(lhs.getSort())) {
			return bitvectorEquality(script, lhs, rhs);
		}
		if (SmtSortUtils.isArraySort(lhs.getSort())) {
			return arrayEquality(script, lhs, rhs);
		}
		return script.term("=", CommuhashUtils.sortByHashCode(lhs, rhs));
	}

	/**
	 * Returns the negated equality (not ("=" lhs rhs)), or true resp. false if some simple checks detect validity or
	 * unsatisfiablity of the equality. We deliberately do not return the "distinct" function from SMT-LIB. In Ultimate
	 * we prefer explicit negations, because these can help us detect inconsitencies between terms syntactically.
	 */
	public static Term distinct(final Script script, final Term lhs, final Term rhs) {
		return SmtUtils.not(script, binaryEquality(script, lhs, rhs));
	}

	/**
	 * Returns the equality ("=" lhs rhs), but checks if one of the arguments is true/false and simplifies accordingly.
	 */
	private static Term booleanEquality(final Script script, final Term lhs, final Term rhs) {
		if (isTrueLiteral(lhs)) {
			return rhs;
		}
		if (isFalseLiteral(lhs)) {
			return SmtUtils.not(script, rhs);
		}
		if (isTrueLiteral(rhs)) {
			return lhs;
		}
		if (isFalseLiteral(rhs)) {
			return SmtUtils.not(script, lhs);
		}
		return script.term("=", CommuhashUtils.sortByHashCode(lhs, rhs));
	}

	/**
	 * Returns the equality ("=" lhs rhs), for inputs of sort BitVec. Simplifies if both inputs are literals.
	 */
	private static Term bitvectorEquality(final Script script, final Term lhs, final Term rhs) {
		if (!SmtSortUtils.isBitvecSort(lhs.getSort())) {
			throw new UnsupportedOperationException("need BitVec sort");
		}
		if (!SmtSortUtils.isBitvecSort(rhs.getSort())) {
			throw new UnsupportedOperationException("need BitVec sort");
		}
		return PolynomialRelation.of(script, RelationSymbol.EQ, lhs, rhs).toTerm(script);
	}

	/**
	 * Returns the equality ("=" lhs rhs), for inputs of numeric sort (int, real) Simplifies if both inputs are
	 * literals.
	 */
	private static Term numericEquality(final Script script, final Term lhs, final Term rhs) {
		if (!lhs.getSort().isNumericSort()) {
			throw new UnsupportedOperationException("need numeric sort");
		}
		if (!rhs.getSort().isNumericSort()) {
			throw new UnsupportedOperationException("need numeric sort");
		}
		return PolynomialRelation.of(script, RelationSymbol.EQ, lhs, rhs).toTerm(script);
	}

	/**
	 * Returns the equality ("=" lhs rhs), for inputs of array sort. If the term if of the form ("=" a ("store" a k v))
	 * it is simplified to ("=" ("select" a k) v). Rationale: the latter term is simpler than the first term for our
	 * algorithms
	 */
	private static Term arrayEquality(final Script script, final Term lhs, final Term rhs) {
		if (!lhs.getSort().isArraySort()) {
			throw new UnsupportedOperationException("need array sort");
		}
		if (!rhs.getSort().isArraySort()) {
			throw new UnsupportedOperationException("need array sort");
		}
		if (lhs instanceof ApplicationTerm) {
			final ApplicationTerm appLhs = (ApplicationTerm) lhs;
			if ("store".equals(appLhs.getFunction().getName()) && appLhs.getParameters()[0] == rhs) {
				return setArrayCellValue(script, appLhs.getParameters()[0], appLhs.getParameters()[1],
						appLhs.getParameters()[2]);
			}
		}
		if (rhs instanceof ApplicationTerm) {
			final ApplicationTerm appRhs = (ApplicationTerm) rhs;
			if ("store".equals(appRhs.getFunction().getName()) && appRhs.getParameters()[0] == lhs) {
				return setArrayCellValue(script, appRhs.getParameters()[0], appRhs.getParameters()[1],
						appRhs.getParameters()[2]);
			}
		}
		return script.term("=", CommuhashUtils.sortByHashCode(lhs, rhs));
	}

	/**
	 * @return ("=" ("select" array index) value)
	 */
	private static Term setArrayCellValue(final Script script, final Term array, final Term index, final Term value) {
		final Term select = SmtUtils.select(script, array, index);
		return SmtUtils.binaryEquality(script, select, value);
	}

	/**
	 * Removes vertical bars from a String. In SMT-LIB identifiers can be quoted using | (vertical bar) and vertical
	 * bars must not be nested.
	 */
	public static String removeSmtQuoteCharacters(final String string) {
		return string.replaceAll("\\|", "");
	}

	public static Map<TermVariable, Term> termVariables2Constants(final Script script,
			final Collection<TermVariable> termVariables, final boolean declareConstants) {
		final Map<TermVariable, Term> mapping = new HashMap<>();
		for (final TermVariable tv : termVariables) {
			final Term constant = termVariable2constant(script, tv, declareConstants);
			mapping.put(tv, constant);
		}
		return mapping;
	}

	public static Term termVariable2constant(final Script script, final TermVariable tv,
			final boolean declareConstant) {
		final String name = removeSmtQuoteCharacters(tv.getName());
		if (declareConstant) {
			final Sort resultSort = tv.getSort();
			script.declareFun(name, new Sort[0], resultSort);
		}
		return script.term(name);
	}

	/**
	 * Returns true, iff the term contains an application of the given functionName
	 */
	public static boolean containsFunctionApplication(final Term term, final String functionName) {
		return !extractApplicationTerms(functionName, term, true).isEmpty();
	}

	/**
	 * Returns true, iff the term contains an application of at least one of the the given functionNames
	 */
	public static boolean containsFunctionApplication(final Term term, final Collection<String> functionNames) {
		return functionNames.stream().anyMatch(x -> containsFunctionApplication(term, x));
	}

	public static boolean containsArrayVariables(final Term... terms) {
		for (final Term term : terms) {
			for (final TermVariable tv : term.getFreeVars()) {
				if (tv.getSort().isArraySort()) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Returns true, iff the term is array-free. This is the case, if no array variables, no select- and no
	 * store-expressions are found in it.
	 */
	public static boolean isArrayFree(final Term term) {
		return !containsArrayVariables(term) && !containsFunctionApplication(term, Arrays.asList("select", "store"));
	}

	/**
	 * Returns true, iff the term contains an UF-application
	 */
	public static boolean containsUninterpretedFunctionApplication(final Term term) {
		for (final NonTheorySymbol<?> s : new NonTheorySymbolFinder().findNonTheorySymbols(term)) {
			if (s instanceof NonTheorySymbol.Function) {
				return true;
			}
		}
		return false;
	}

	public static boolean isFalseLiteral(final Term term) {
		return isLiteral("false", term);
	}

	public static boolean isTrueLiteral(final Term term) {
		return isLiteral("true", term);
	}

	private static boolean isLiteral(final String literal, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fun = appTerm.getFunction();
			return fun.getParameterSorts().length == 0 && literal.equals(fun.getApplicationString());
		}
		return false;
	}

	/**
	 * A constant is an ApplicationTerm with zero parameters whose function symbol is not intern.
	 */
	public static boolean isConstant(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return appTerm.getParameters().length == 0 && !appTerm.getFunction().isIntern();
		}
		return false;
	}

	/**
	 * @return true iff term is some literal of sort Int whose value is the input number.
	 */
	public static boolean isIntegerLiteral(final BigInteger number, final Term term) {
		if (term instanceof ConstantTerm && SmtSortUtils.isIntSort(term.getSort())) {
			final Object value = ((ConstantTerm) term).getValue();
			if (value instanceof Rational) {
				return value.equals(Rational.valueOf(number, BigInteger.ONE));
			}
			if (value instanceof BigInteger) {
				return value.equals(number);
			}
			throw new AssertionError("unknown type of integer value " + value.getClass().getSimpleName());
		}
		return false;
	}

	/**
	 * @param term
	 *            A {@link Term} whose {@link Sort} is "Bool". For other {@link Sort}s the notion of atomicity is not
	 *            defined
	 * @return true iff the given term is an atomic formula, which means it does not contain any logical symbols (e.g.,
	 *         and, or, not, implication, biimplication, quantifiers) FIXME 2017-07-31 Matthias: provides incorrect
	 *         result for user defined or theory defined (does such a theory exists?) function symbols with Boolean
	 *         parameters.
	 */
	public static boolean isAtomicFormula(final Term term) {
		if (SmtSortUtils.isBoolSort(term.getSort())) {
			if (isTrueLiteral(term) || isFalseLiteral(term)) {
				return true;
			}
			if (term instanceof TermVariable || isConstant(term)) {
				return true;
			}
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (NonCoreBooleanSubTermTransformer.isCoreBooleanNonAtom(appTerm)) {
					return false;
				}
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns true iff the given term is in NNF (only {@code and}, {@code or} and {@code not} as logical operators,
	 * where only atoms occurs after a {@code not}).
	 */
	public static boolean isNNF(final Term term) {
		for (final String f : Arrays.asList("=", "=>", "xor", "distinct", "ite")) {
			for (final Term t : extractApplicationTerms(f, term, true)) {
				if (allParamsAreBool((ApplicationTerm) t)) {
					return false;
				}
			}
		}
		for (final Term t : extractApplicationTerms("not", term, true)) {
			if (!isAtomicFormula(((ApplicationTerm) t).getParameters()[0])) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Return all free TermVariables that occur in a set of Terms.
	 */
	public static Set<TermVariable> getFreeVars(final Collection<Term> terms) {
		final Set<TermVariable> freeVars = new HashSet<>();
		for (final Term term : terms) {
			freeVars.addAll(Arrays.asList(term.getFreeVars()));
		}
		return freeVars;
	}

	public static Term and(final Script script, final Term... terms) {
		if (EXTENDED_LOCAL_SIMPLIFICATION) {
			return andWithExtendedLocalSimplification(script, Arrays.asList(terms));
		}
		return Util.and(script, terms);
	}

	public static Term and(final Script script, final Collection<Term> terms) {
		if (EXTENDED_LOCAL_SIMPLIFICATION) {
			return andWithExtendedLocalSimplification(script, terms);
		}
		return Util.and(script, terms.toArray(new Term[terms.size()]));
	}

	public static Term or(final Script script, final Term... terms) {
		if (EXTENDED_LOCAL_SIMPLIFICATION) {
			return orWithExtendedLocalSimplification(script, Arrays.asList(terms));
		}
		return Util.or(script, terms);
	}

	public static Term or(final Script script, final Collection<Term> terms) {
		if (EXTENDED_LOCAL_SIMPLIFICATION) {
			return orWithExtendedLocalSimplification(script, terms);
		}
		return Util.or(script, terms.toArray(new Term[terms.size()]));
	}

	public static Term andWithExtendedLocalSimplification(final Script script, final Term... terms) {
		return andWithExtendedLocalSimplification(script, Arrays.asList(terms));
	}

	public static Term andWithExtendedLocalSimplification(final Script script, final Collection<Term> terms) {
		final Set<Term> resultJuncts = new HashSet<>();
		final Set<Term> negativeJuncts = new HashSet<>();
		final InnerDualJunctTracker idjt = new InnerDualJunctTracker();
		final String connective = "and";
		final Predicate<Term> isNeutral = SmtUtils::isTrueLiteral;
		final Predicate<Term> isAbsorbing = SmtUtils::isFalseLiteral;
		final boolean resultIsAbsorbingElement = recursiveAndOrSimplificationHelper(script, connective, isNeutral,
				isAbsorbing, terms, resultJuncts, negativeJuncts, idjt);
		if (resultIsAbsorbingElement) {
			return script.term("false");
		}
		if (resultJuncts.isEmpty()) {
			return script.term("true");
		}
		if (resultJuncts.size() == 1) {
			return resultJuncts.iterator().next();
		}
		final boolean applyDistributivity = false;
		if (applyDistributivity && idjt.getInnerDualJuncts() != null && !idjt.getInnerDualJuncts().isEmpty()) {
			return applyDistributivity(script, resultJuncts, connective, idjt.getInnerDualJuncts());
		}
		return script.term(connective,
				CommuhashUtils.sortByHashCode(resultJuncts.toArray(new Term[resultJuncts.size()])));
	}

	private static Term applyDistributivity(final Script script, final Set<Term> dualJunctions,
			final String outerConnective, final Set<Term> omnipresentInnerDualJuncts) {
		final String innerConnective = QuantifierUtils.getDualBooleanConnective(outerConnective);
		final Term[] resultDualJunctions = new Term[dualJunctions.size()];
		int outerOffset = 0;
		for (final Term dualJunction : dualJunctions) {
			final Term[] innerDualJuncts = QuantifierUtils
					.getDualFiniteJuncts(QuantifierUtils.getCorrespondingQuantifier(outerConnective), dualJunction);
			final Term[] remainingInnerDualJuncts =
					new Term[innerDualJuncts.length - omnipresentInnerDualJuncts.size()];
			int offset = 0;
			for (final Term innerDualJunct : innerDualJuncts) {
				if (!omnipresentInnerDualJuncts.contains(innerDualJunct)) {
					remainingInnerDualJuncts[offset] = innerDualJunct;
					offset++;
				}
			}
			if (remainingInnerDualJuncts.length == 0) {
				throw new AssertionError("optimization!!");
			}
			if (remainingInnerDualJuncts.length == 1) {
				resultDualJunctions[outerOffset] = remainingInnerDualJuncts[0];
			} else {
				resultDualJunctions[outerOffset] = script.term(innerConnective, remainingInnerDualJuncts);
			}
			outerOffset++;
		}
		final Term resultInnerDistributed = script.term(outerConnective, resultDualJunctions);
		final List<Term> resultOuter = new ArrayList<>(omnipresentInnerDualJuncts.size() + 1);
		resultOuter.addAll(omnipresentInnerDualJuncts);
		resultOuter.add(resultInnerDistributed);
		return script.term(innerConnective, resultOuter.toArray(new Term[resultOuter.size()]));
	}

	public static Term orWithExtendedLocalSimplification(final Script script, final Collection<Term> terms) {
		final Set<Term> resultJuncts = new HashSet<>();
		final Set<Term> negativeJuncts = new HashSet<>();
		final InnerDualJunctTracker idjt = new InnerDualJunctTracker();
		final String connective = "or";
		final Predicate<Term> isNeutral = SmtUtils::isFalseLiteral;
		final Predicate<Term> isAbsorbing = SmtUtils::isTrueLiteral;
		final boolean resultIsAbsorbingElement = recursiveAndOrSimplificationHelper(script, connective, isNeutral,
				isAbsorbing, terms, resultJuncts, negativeJuncts, idjt);
		if (resultIsAbsorbingElement) {
			return script.term("true");
		}
		if (resultJuncts.isEmpty()) {
			return script.term("false");
		}
		if (resultJuncts.size() == 1) {
			return resultJuncts.iterator().next();
		}
		return script.term(connective,
				CommuhashUtils.sortByHashCode(resultJuncts.toArray(new Term[resultJuncts.size()])));
	}

	/**
	 * Auxiliary method for constructing simplified versions of conjunctions and disjunctions. Does the following
	 * simplications
	 * <ul>
	 * <li>if some junct is neutral element, we can omit it (e.g., we can drop "true" from conjunctions)
	 * <li>if some junct is absorbing element, result is equivalent to absorbing element (e.g., "x=0 /\ false" is
	 * equivalent to "false")
	 * <li>if some junct is has the same connective, we can flatten it (e.g., "((A /\ B) /\ C)" is equivalent to "(A /\
	 * B /\ C)")
	 * <li>if some junct and its negation occur, the result is equivalent to the absorbing element (e.g., "A /\ (not A)"
	 * is equivalent to "false")
	 * <li>if some junct occurs twice we can drop one occurrence. (e.g., "A /\ A" is equivalent to "A")
	 * </ul>
	 *
	 * @param connective
	 *            either "and" or "or"
	 * @param isNeutral
	 *            {@link Predicate} that is true iff input is the neutral element wrt. the connective ("true" is neutral
	 *            for "and", "false" is neutral for "or")
	 * @param isAbsorbing
	 *            {@link Predicate} that is true iff input is the absorbing element wrt. the connective ("false" is
	 *            absorbing for "and", "true" is absorbing for "or")
	 * @param inputJuncts
	 *            disjuncts or conjuncts that are the input to this simplification
	 * @param resultJuncts
	 *            disjuncts or conjuncts that will belong to the final output
	 * @param negatedJuncts
	 *            arguments of juncts whose connective is "not"
	 * @return true iff we detected that the result is equivalent to the absorbing element of the connective
	 */
	private static boolean recursiveAndOrSimplificationHelper(final Script script, final String connective,
			final Predicate<Term> isNeutral, final Predicate<Term> isAbsorbing, final Collection<Term> inputJuncts,
			final Set<Term> resultJuncts, final Set<Term> negatedJuncts, final InnerDualJunctTracker idjt) {
		for (final Term junct : inputJuncts) {
			if (isNeutral.test(junct)) {
				// do nothing, junct will not contribute to result
				continue;
			}
			if (isAbsorbing.test(junct)) {
				// result will be equivalent to absorbing element
				return true;
			}
			if (junct instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) junct;
				if (appTerm.getFunction().getName().equals(connective)) {
					// current junct has same connective as result
					// descend recusively to check and add its subjuncts
					final boolean resultIsAbsorbingElement =
							recursiveAndOrSimplificationHelper(script, connective, isNeutral, isAbsorbing,
									Arrays.asList(appTerm.getParameters()), resultJuncts, negatedJuncts, idjt);
					if (resultIsAbsorbingElement) {
						return true;
					}
					// the recursive all added all subjuncts,
					// no need to add the junct itself
					continue;
				}
				if ("not".equals(appTerm.getFunction().getName())) {
					if (resultJuncts.contains(appTerm.getParameters()[0])) {
						// we already have the argument of this not term in the resultJuncts,
						// hence the result will be equivalent to the absorbing element
						return true;
					}
					negatedJuncts.add(appTerm.getParameters()[0]);
				}
			}
			if (negatedJuncts.contains(junct)) {
				// we already have the negation of this junct in the resultJuncts,
				// hence the result will be equivalent to the absorbing element
				return true;
			}
			resultJuncts.add(junct);
			idjt.addOuterJunct(junct, connective);
		}
		return false;
	}

	/**
	 * Copy of {@link Util#ite} that uses our library methods for the construction of terms.
	 */
	public static Term ite(final Script script, final Term cond, final Term thenPart, final Term elsePart) {
		if (isTrueLiteral(cond) || thenPart == elsePart) {
			return thenPart;
		} else if (isFalseLiteral(cond)) {
			return elsePart;
		} else if (isTrueLiteral(thenPart)) {
			return or(script, cond, elsePart);
		} else if (isFalseLiteral(elsePart)) {
			return and(script, cond, thenPart);
		} else if (isFalseLiteral(thenPart)) {
			return and(script, not(script, cond), elsePart);
		} else if (isTrueLiteral(elsePart)) {
			return or(script, not(script, cond), thenPart);
		}
		return script.term("ite", cond, thenPart, elsePart);
	}

	/**
	 * @return term that is equivalent to lhs <= rhs
	 */
	public static Term leq(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "<=", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs >= rhs
	 */
	public static Term geq(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, ">=", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs < rhs
	 */
	public static Term less(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "<", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs > rhs
	 */
	public static Term greater(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, ">", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvule lhs rhs) TODO move to BitvectorUtils/optimize
	 */
	public static Term bvule(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvule", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvult lhs rhs)
	 */
	public static Term bvult(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvult", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvuge lhs rhs)
	 */
	public static Term bvuge(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvuge", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvugt lhs rhs)
	 */
	public static Term bvugt(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvugt", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvsle lhs rhs)
	 */
	public static Term bvsle(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvsle", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvsle lhs rhs)
	 */
	public static Term bvslt(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvslt", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvsge lhs rhs)
	 */
	public static Term bvsge(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvsge", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to (bvsge lhs rhs)
	 */
	public static Term bvsgt(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "bvsgt", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs X rhs where X is either leq, less, geq, or greater.
	 */
	private static Term comparison(final Script script, final String functionSymbol, final Term lhs, final Term rhs) {
		final RelationSymbol rel = RelationSymbol.convert(functionSymbol);
		if (rel == null) {
			throw new AssertionError("Unknown RelationSymbol" + functionSymbol);
		}
		if (!rel.isConvexInequality()) {
			throw new AssertionError("Not a comparison " + functionSymbol);
		}
		if (lhs == rhs) {
			// This check is helpful for bitvector inequalities which cannot be converted to
			// PolynomialRelations.
			if (rel.isStrictRelation()) {
				return script.term("false");
			} else {
				return script.term("true");
			}
		}
		if (SmtSortUtils.isNumericSort(lhs.getSort())) {
			return PolynomialRelation.of(script, RelationSymbol.convert(functionSymbol), lhs, rhs)
					.toTerm(script);
		} else {
			assert SmtSortUtils.isBitvecSort(lhs.getSort());
			// TODO 20220908 Matthias: Minor improvements still possible. E.g., everything
			// is bvule 0.
			return script.term(functionSymbol, lhs, rhs);
		}
	}

	/**
	 * Declare and return a new constant. A constant is a 0-ary application term.
	 *
	 * @param name
	 *            name of the resulting constant
	 * @param sort
	 *            the sort of the resulting constant
	 * @return resulting constant as a ApplicationTerm
	 * @throws SMTLIBException
	 *             if declaration of constant fails, e.g. the name is already defined
	 */
	public static ApplicationTerm buildNewConstant(final Script script, final String name, final String sortname) {
		script.declareFun(name, new Sort[0], script.sort(sortname));
		return (ApplicationTerm) script.term(name);
	}

	/**
	 * Auxiliary method for {@link TermTransformer}. The method {@link TermTransformer#convertApplicationTerm}
	 * constructs new terms that may violate the Ultimate Normal Form (UNF) {@link UltimateNormalFormUtils}. Classes in
	 * Ultimate that inherit {@link TermTransformer} should overwrite {@link TermTransformer#convertApplicationTerm} by
	 * a method that uses this method for the construction of new terms. See e.g., {@link Substitution}.
	 *
	 * @param appTerm
	 *            original ApplicationTerm
	 * @param newArgs
	 *            parameters of the transformed ApplicationTerm
	 */
	public static Term convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs,
			final Script script) {
		final Term result;
		final Term[] oldArgs = appTerm.getParameters();
		if (oldArgs == newArgs) {
			// no argument was changed, we can return the original term
			result = appTerm;
		} else {
			result = SmtUtils.unfTerm(script, appTerm.getFunction(), newArgs);
		}
		return result;
	}

	/**
	 * Variation of {@link SmtUtils#unfTerm(Script, String, String[], Sort, Term...)} for the case that you already have
	 * a {@link FunctionSymbol}.
	 */
	public static Term unfTerm(final Script script, final FunctionSymbol fun, final Term... params) {
		final Sort resultSort = fun.isReturnOverload() ? fun.getReturnSort() : null;
		return unfTerm(script, fun.getName(), fun.getIndices(), resultSort, params);
	}

	/**
	 * Ultimate's default method for constructing terms. In contrast to {@link Script#term} this method applies some
	 * lightweight simplifications and ensures that the output is in Ultimate normal form (UNF) if the input was in UNF.
	 * This method applies only simplifications that do will slow down the performance significantly. <br />
	 * You should only apply {@link Script#term} instead of this method in the following two cases.
	 * <li>You want to construct a term that has to have the syntactic form specified by your arguments. (Note that this
	 * might violate the UNF and some of your algorithms will not be able to process your term.)
	 * <li>You implement a method in this package that is (transitively) called by this method (needed to avoid infinite
	 * loops) and you take care by yourself that the UNF is preserved.
	 *
	 * @param resultSort
	 *            must be non-null if and only if we have an explicitly instantiated polymorphic FunctionSymbol, i.e., a
	 *            function of the form `(as <name> <sort>)`
	 */
	public static Term unfTerm(final Script script, final String funcname, final String[] indices,
			final Sort resultSort, final Term... params) {
		final Term result;
		switch (funcname) {
		case "and":
			result = SmtUtils.and(script, params);
			break;
		case "or":
			result = SmtUtils.or(script, params);
			break;
		case "not":
			if (params.length != 1) {
				throw new IllegalArgumentException("no not term");
			}
			result = SmtUtils.not(script, params[0]);
			break;
		case "=":
			if (params.length != 2) {
				throw new UnsupportedOperationException(
						"not yet implemented: equality with " + params.length + " params");
			}
			result = binaryEquality(script, params[0], params[1]);
			break;
		case "distinct":
			if (params.length != 2) {
				throw new UnsupportedOperationException(
						"not yet implemented: distinct with " + params.length + " params");
			}
			result = SmtUtils.distinct(script, params[0], params[1]);
			break;
		case "=>":
			result = Util.implies(script, params);
			break;
		case "ite":
			if (params.length != 3) {
				throw new IllegalArgumentException("no ite");
			}
			result = SmtUtils.ite(script, params[0], params[1], params[2]);
			break;
		case "+":
			result = SmtUtils.sum(script, funcname, params);
			break;
		case "-":
			if (params.length == 1) {
				result = SmtUtils.unaryNumericMinus(script, params[0]);
			} else {
				result = SmtUtils.minus(script, params);
			}
			break;
		case "*":
			result = SmtUtils.mul(script, funcname, params);
			break;
		case "div":
			if (params.length < 2) {
				throw new IllegalArgumentException("div needs at least two arguments");
			}
			result = divInt(script, params);
			break;
		case "mod":
			if (params.length != 2) {
				throw new IllegalArgumentException("no mod");
			}
			result = mod(script, params[0], params[1]);
			break;
		case ">=":
		case "<=":
		case ">":
		case "<":
			if (params.length != 2) {
				throw new IllegalArgumentException("no comparison");
			}
			result = comparison(script, funcname, params[0], params[1]);
			break;
		case "store":
			result = store(script, params[0], params[1], params[2]);
			break;
		case "select":
			result = select(script, params[0], params[1]);
			break;
		case "zero_extend":
		case "extract":
		case "bvadd":
		case "bvsub":
		case "bvmul":
		case "bvudiv":
		case "bvurem":
		case "bvsdiv":
		case "bvsrem":
		case "bvsmod":
		case "bvand":
		case "bvor":
		case "bvxor":
		case "bvnot":
		case "bvneg":
		case "bvshl":
		case "bvlshr":
		case "bvashr":
		case "bvult":
		case "bvule":
		case "bvugt":
		case "bvuge":
		case "bvslt":
		case "bvsle":
		case "bvsgt":
		case "bvsge":
			result = BitvectorUtils.unfTerm(script, funcname, toBigIntegerArray(indices), params);
			break;
		default:
			result = script.term(funcname, indices, resultSort, params);
			break;
		}
		assert !DEBUG_ASSERT_ULTIMATE_NORMAL_FORM
				|| UltimateNormalFormUtils.respectsUltimateNormalForm(result) : "Term not in UltimateNormalForm";

		assert !DEBUG_CHECK_EVERY_SIMPLIFICATION || Util.checkSat(script,
				script.term("distinct", result, script.term(funcname, indices, resultSort, params))) != LBool.SAT;
		return result;
	}

	public static Term select(final Script script, final Term array, final Term index) {
		final Term result;
		if (FLATTEN_ARRAY_TERMS) {
			final ArrayStore as = ArrayStore.of(array);
			if (as != null) {
				result = selectOverStore(script, as, index);
			} else {
				result = script.term("select", array, index);
			}
		} else {
			result = script.term("select", array, index);
		}
		return result;
	}

	private static Term selectOverStore(final Script script, final ArrayStore as, final Term index) {
		final Term result;
		// Check for select-over-store
		if (as.getIndex().equals(index)) {
			// Found select-over-store => ignore inner store
			// => transform into value
			result = as.getValue();
		} else {
			final IPolynomialTerm selectIndex = PolynomialTermTransformer.convert(script, index);
			final IPolynomialTerm storeIndex = PolynomialTermTransformer.convert(script, as.getIndex());
			if (selectIndex == null || storeIndex == null) {
				result = script.term("select", as.getTerm(), index);
			} else {
				final Equivalence comparison = selectIndex.compare(storeIndex);
				switch (comparison) {
				case DISTINCT:
					result = select(script, as.getArray(), index);
					break;
				case EQUALS:
					result = as.getValue();
					break;
				case INCOMPARABLE:
					result = script.term("select", as.getTerm(), index);
					break;
				default:
					throw new AssertionError("unknown value " + comparison);
				}
			}
		}
		return result;
	}

	/**
	 * Construct store term from the array theory. Uses an optimization for
	 * (syntactically) similar indices. E.g., if we have a store term of the form
	 * `(store (store (store (store a k 0) j 1) k 2) j 3)`, the two innermost store
	 * terms are dropped because the outer store terms use also index k and j.
	 */
	public static Term store(final Script script, final Term array, final Term index, final Term value) {
		ArrayStore as = ArrayStore.of(array);
		if (as == null) {
			// no nested store
			return script.term("store", array, index, value);
		}
		final Set<Term> indices = new HashSet<>();
		indices.add(index);
		// index-value pairs that we will have in the result, pairs of inner stores
		// at the beginning
		final ArrayDeque<Pair<Term, Term>> indexValueSequence = new ArrayDeque<>();
		indexValueSequence.addFirst(new Pair<>(index, value));
		Term currentArray = array;
		while (as != null) {
			// for indices that occurred already in the outer stores, we drop the inner
			// index-value pairs
			if (!indices.contains(as.getIndex())) {
				indexValueSequence.addFirst(new Pair<>(as.getIndex(), as.getValue()));
				indices.add(as.getIndex());
			}
			currentArray = as.getArray();
			as = ArrayStore.of(currentArray);
		}
		Term result = currentArray;
		for (final Pair<Term, Term> indexValue : indexValueSequence) {
			result = script.term("store", result, indexValue.getFirst(), indexValue.getSecond());
		}
		return result;
	}

	/**
	 * @return idx if array has form (store a idx v) return null if array has a different form
	 */
	public static Term getArrayStoreIdx(final Term array) {
		if (array instanceof ApplicationTerm) {
			final ApplicationTerm appArray = (ApplicationTerm) array;
			final FunctionSymbol arrayFunc = appArray.getFunction();
			if (arrayFunc.isIntern() && "store".equals(arrayFunc.getName())) {
				// (store a i v)
				return appArray.getParameters()[1];
			}
		}
		return null;
	}

	/**
	 * Takes a Term with array sort and unwraps all select and store terms until it hits the TermVariable or
	 * ConstantTerm that can no longer be unwrapped. Examples: let a be an array variable, i1, i2, v some terms
	 * <ul>
	 * <li>a returns a
	 * <li>(store a i v) returns a
	 * <li>(store (select a i1) i2 v) returns a
	 * </ul>
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 * @return the simple array term inside the given array term that is obtained by taking the first argument of store
	 *         and select terms exhaustively.
	 */
	public static Term getBasicArrayTerm(final Term possiblyComplexArrayTerm) {
		assert possiblyComplexArrayTerm.getSort().isArraySort();
		Term result = possiblyComplexArrayTerm;
		while (SmtUtils.isFunctionApplication(result, "store") || SmtUtils.isFunctionApplication(result, "select")) {
			result = ((ApplicationTerm) result).getParameters()[0];
		}
		assert result.getSort().isArraySort();
		assert result instanceof TermVariable || result instanceof ConstantTerm || isConstant(result);
		return result;
	}

	/**
	 * Checks if the given {@link Term} is a basic array term (i.e. a constant or a variable with an array sort). (In
	 * the same sense as in {@link #getBasicArrayTerm(Term)})
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 * @param term
	 * @return true if term is a basic array term
	 */
	public static boolean isBasicArrayTerm(final Term term) {
		if (!term.getSort().isArraySort()) {
			return false;
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			if (at.getParameters().length > 0) {
				return false;
			}
			// term is a constant
		}
		assert term instanceof ApplicationTerm || term instanceof TermVariable || term instanceof ConstantTerm;

		return true;
	}

	public static String sanitizeStringAsSmtIdentifier(final String name) {
		return name.replaceAll("\\|", "BAR").replaceAll(" ", "_");
	}

	public static Term abs(final Script script, final Term operand) {
		if (operand instanceof ConstantTerm && SmtSortUtils.isIntSort(operand.getSort())) {
			final Rational operandAsRational = toRational((ConstantTerm) operand);
			return operandAsRational.abs().toTerm(operand.getSort());
		}
		return script.term("abs", operand);
	}

	/**
	 * Division for reals with the following simplifications.
	 * <ul>
	 * <li>Initial literals are simplified by division.
	 * <li>A non-initial zero cannot be simplified (semantics of division by zero similar to uninterpreted function see
	 * http://smtlib.cs.uiowa.edu/theories-Reals.shtml). This means especially that an initial zero does not make the
	 * result zero, because 0.0 is not equivalent to (/ 0.0 0.0).
	 * <li>An intermediate 1.0 literal is dropped.
	 * <li>Intermediate literals are simplified by multiplication.
	 * </ul>
	 *
	 * See {@link SmtUtilsTest#divRealTest01} for tests. TODO: Apply flattening such that (div (div x y) z) becomes (div
	 * x y z).
	 */
	public static Term divReal(final Script script, final Term... inputParams) {
		final List<Term> resultParams = new ArrayList<>();
		if (inputParams.length == 0) {
			throw new IllegalArgumentException("real division needs at least one argument");
		}
		resultParams.add(inputParams[0]);
		for (int i = 1; i < inputParams.length; i++) {
			final Rational nextAsRational = tryToConvertToLiteral(inputParams[i]);
			if (nextAsRational == null) {
				// cannot simplify - is not at literal
				resultParams.add(inputParams[i]);
			} else if (nextAsRational.numerator() == BigInteger.ZERO) {
				// cannot simplify
				resultParams.add(inputParams[i]);
			} else if (nextAsRational.numerator() == BigInteger.ONE && nextAsRational.isIntegral()) {
				// do nothing
			} else {
				final Rational lastSimplifiedParam;
				if (resultParams.isEmpty()) {
					lastSimplifiedParam = null;
				} else {
					final Rational tmp = tryToConvertToLiteral(resultParams.get(resultParams.size() - 1));
					if (tmp == null) {
						lastSimplifiedParam = null;
					} else // if parameter at position i-1 is zero we can use
					// it for simplification iff it will be the first
					// parameter of the result (i.e., we do not divide
					// by 0)
					if (!tmp.numerator().equals(BigInteger.ZERO) || resultParams.size() == 1) {
						lastSimplifiedParam = tmp;
					} else {
						lastSimplifiedParam = null;
					}
				}
				if (lastSimplifiedParam != null) {
					// if parameter at position i-1 is the first parameter
					// (i.e., i=1) we divide it by the next parameter
					// otherwise we multiply with the next parameter
					// e.g., 54/2 becomes 23, but x/21/2 becomes x/42
					final Rational resultRat;
					if (resultParams.size() == 1) {
						resultRat = lastSimplifiedParam.div(nextAsRational);
					} else {
						resultRat = lastSimplifiedParam.mul(nextAsRational);
					}
					final Term resultTerm = resultRat.toTerm(SmtSortUtils.getRealSort(script));
					resultParams.set(resultParams.size() - 1, resultTerm);
				} else {
					// cannot simplify
					resultParams.add(inputParams[i]);
				}
			}
		}
		if (resultParams.size() == 1) {
			return resultParams.get(0);
		}
		return script.term("/", resultParams.toArray(new Term[resultParams.size()]));
	}

	/**
	 * Division for ints with the several simplifications.
	 */
	public static Term divInt(final Script script, final Term... inputParams) {
		final AbstractGeneralizedAffineTerm<?>[] polynomialArgs =
				new AbstractGeneralizedAffineTerm<?>[inputParams.length];
		for (int i = 0; i < inputParams.length; i++) {
			polynomialArgs[i] =
					(AbstractGeneralizedAffineTerm<?>) PolynomialTermTransformer.convert(script, inputParams[i]);
		}
		return polynomialArgs[0].div(script, Arrays.copyOfRange(polynomialArgs, 1, polynomialArgs.length))
				.toTerm(script);
	}

	/**
	 * Convert `(div (div a1 ... an) d)` to `(div a1 ... d*an)` if `an` and `d` are non-zero literals and convert it to
	 * `(div a1 ... an d)` otherwise.
	 */
	public static Term divIntFlatten(final Script script, final Term divident, final Term divisor) {
		final Rational divisorRat = SmtUtils.tryToConvertToLiteral(divisor);
		Term result;
		if (divisorRat != null) {
			final BigInteger divisorBigInt = divisorRat.numerator();
			result = divIntFlatten(script, divident, divisorBigInt);
		} else {
			final ApplicationTerm divTerm = SmtUtils.getFunctionApplication(divident, "div");
			if (divTerm != null) {
				final List<Term> divArguments = new ArrayList<>(Arrays.asList(divTerm.getParameters()));
				if (divArguments.size() < 2) {
					throw new AssertionError();
				}
				divArguments.add(divisor);
				// Can't be simplified.
				// Do not use {@link SmtUtils#div} to avoid nonterminating loop.
				result = script.term("div", divArguments.toArray(new Term[divArguments.size()]));
			} else {
				// Can't be simplified.
				// Do not use {@link SmtUtils#div} to avoid nonterminating loop.
				result = script.term("div", divident, divisor);
			}
		}
		return result;
	}

	/**
	 * Convert `(div (div a1 ... an) d)` to `(div a1 ... d*an)` if `an` is a
	 * positive literal and convert it to `(div a1 ... an d)` otherwise. Note that
	 * the similar transformation would be unsound for negative literals, see
	 * {@link PolynomialTest#intDivision10}
	 */
	public static Term divIntFlatten(final Script script, final Term divident, final BigInteger divisorBigInt) {
		final Term result;
		final ApplicationTerm divTerm = SmtUtils.getFunctionApplication(divident, "div");
		if (divTerm != null) {
			final List<Term> divArguments = new ArrayList<>(Arrays.asList(divTerm.getParameters()));
			if (divArguments.size() < 2) {
				throw new AssertionError();
			}
			final Term lastElement = divArguments.get(divArguments.size() - 1);
			final Rational lastElementRat = SmtUtils.tryToConvertToLiteral(lastElement);
			if (lastElementRat != null && lastElementRat.compareTo(Rational.ONE) >= 0) {
				final BigInteger lastElementBigInteger = lastElementRat.numerator();
				final BigInteger newLastElement = lastElementBigInteger.multiply(divisorBigInt);
				divArguments.set(divArguments.size() - 1, SmtUtils.constructIntValue(script, newLastElement));
			} else {
				divArguments.add(SmtUtils.constructIntValue(script, divisorBigInt));
			}
			result = script.term("div", divArguments.toArray(new Term[divArguments.size()]));
		} else {
			result = script.term("div", divident, SmtUtils.constructIntValue(script, divisorBigInt));
		}
		return result;
	}

	/**
	 * Apply division but use some simplifications.
	 */
	public static Term division(final Script script, final Sort sort, final Term... params) {
		if (SmtSortUtils.isRealSort(sort)) {
			return SmtUtils.divReal(script, params);
		}
		if (SmtSortUtils.isIntSort(sort)) {
			return SmtUtils.divInt(script, params);
		}
		if (SmtSortUtils.isBitvecSort(sort)) {
			throw new UnsupportedOperationException(
					"Division with simplifications for bitvectors is not yet supported");
		}
		if (SmtSortUtils.isFloatingpointSort(sort)) {
			throw new UnsupportedOperationException("Division with simplifications for floats is not yet supported");
		}
		throw new AssertionError("Division does not make sense for sort " + sort);
	}

	/**
	 * Returns a possibly simplified version of the Term (mod dividend divisor). See {@link PolynomialTest} for
	 * examples.
	 */
	public static Term mod(final Script script, final Term divident, final Term divisor) {
		final Rational divisorAsRational = tryToConvertToLiteral(divisor);
		if (divisorAsRational == null) {
			// cannot simplify
			return script.term("mod", divident, divisor);
		} else {
			assert divisorAsRational.isIntegral();
			final AbstractGeneralizedAffineTerm<?> agat =
					(AbstractGeneralizedAffineTerm<?>) PolynomialTermTransformer.convert(script, divident);
			return agat.mod(script, divisorAsRational.numerator()).toTerm(script);
		}
	}

	/**
	 * @return A BigDecimal if this rational is representable as a finite BigDecimal, nothing otherwise.
	 */
	public static Optional<BigDecimal> toDecimal(final Rational rational) {
		if (!rational.isRational()) {
			return Optional.empty();
		}
		return Optional.of(new BigDecimal(rational.numerator()).divide(new BigDecimal(rational.denominator())));
	}

	public static BigInteger toInt(final Rational integralRational) {
		if (!integralRational.isIntegral()) {
			throw new IllegalArgumentException("dividend has to be integral");
		}
		if (!integralRational.denominator().equals(BigInteger.ONE)) {
			throw new IllegalArgumentException("denominator has to be one");
		}
		return integralRational.numerator();
	}

	public static Rational toRational(final String realLiteralValue) {
		final String[] twoParts = realLiteralValue.split("/");
		if (twoParts.length == 2) {
			return Rational.valueOf(new BigInteger(twoParts[0]), new BigInteger(twoParts[1]));
		}
		if (twoParts.length == 1) {
			return toRational(new BigDecimal(realLiteralValue));
		}
		throw new IllegalArgumentException("Not a valid real literal value: " + realLiteralValue);
	}

	public static Term rational2Term(final Script script, final Rational rational, final Sort sort) {
		if (SmtSortUtils.isNumericSort(sort)) {
			return rational.toTerm(sort);
		}
		if (!SmtSortUtils.isBitvecSort(sort)) {
			throw new AssertionError(ERROR_MSG_UNKNOWN_SORT + sort);
		}
		if (rational.isIntegral() && rational.isRational()) {
			return BitvectorUtils.constructTerm(script, rational.numerator(), sort);
		}
		throw new IllegalArgumentException("unable to convert rational to bitvector if not integer");
	}

	/**
	 * Check if term represents a literal. If this is the case, then return its value as a {@link Rational} otherwise
	 * return null.
	 */
	public static Rational tryToConvertToLiteral(final Term term) {
		final Rational result;
		if (SmtSortUtils.isBitvecSort(term.getSort())) {
			final BitvectorConstant bc = BitvectorUtils.constructBitvectorConstant(term);
			if (bc != null) {
				result = Rational.valueOf(bc.getValue(), BigInteger.ONE);
			} else {
				result = null;
			}
		} else if (SmtSortUtils.isNumericSort(term.getSort())) {
			if (term instanceof ConstantTerm) {
				result = SmtUtils.toRational((ConstantTerm) term);
			} else {
				result = null;
			}
		} else {
			result = null;
		}
		return result;
	}

	/**
	 * Check if {@link Term} which may contain free {@link TermVariable}s is satisfiable with respect to the current
	 * assertion stack of {@link Script}. Compute unsat core if unsatisfiable. Use {@link LoggingScript} to see the
	 * input. TODO: Show values of satisfying assignment (including array access) if satisfiable.
	 *
	 * @param term
	 *            may contain free variables
	 */
	public static LBool checkSatDebug(final Script script, final Term term, final ILogger logger) {
		script.push(1);
		try {
			final TermVariable[] vars = term.getFreeVars();
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final TermVariable var : vars) {
				final Term substituent = termVariable2PseudofreshConstant(script, var);
				substitutionMapping.put(var, substituent);
			}
			final Map<Term, Term> ucMapping = new HashMap<>();
			final Term[] conjuncts = getConjuncts(term);
			for (int i = 0; i < conjuncts.length; i++) {
				final Term conjunct = PureSubstitution.apply(script, substitutionMapping, conjuncts[i]);
				final String name = "conjunct" + i;
				final Annotation annot = new Annotation(":named", name);
				final Term annotTerm = script.annotate(conjunct, annot);
				ucMapping.put(script.term(name), conjuncts[i]);
				script.assertTerm(annotTerm);
			}
			final LBool result = script.checkSat();
			if (result == LBool.UNSAT) {
				final Term[] ucTerms = script.getUnsatCore();
				for (final Term ucTerm : ucTerms) {
					final Term conjunct = ucMapping.get(ucTerm);
					logger.debug("in uc: " + conjunct);
				}
			}
			script.pop(1);
			return result;
		} catch (final Exception e) {
			// unable to recover because assertion stack is modified
			// doing the script.pop(1) in finally block does not make sense
			// since the solver might not be able to respond this will raise
			// another Exception, and we will not see Exception e any more.
			throw new AssertionError("Exception during satisfiablity check: " + e.getMessage());
		}
	}

	private static Term termVariable2PseudofreshConstant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		final Sort resultSort = tv.getSort();
		script.declareFun(name, new Sort[0], resultSort);
		return script.term(name);
	}

	/**
	 * Convert a {@link ConstantTerm} which has numeric {@link Sort} into a {@literal Rational}.
	 *
	 * @return a Rational which represents the input constTerm
	 * @throws UnsupportedOperationException
	 *             if ConstantTerm cannot converted to Rational
	 */
	public static Rational toRational(final ConstantTerm constTerm) {
		assert SmtSortUtils.isNumericSort(constTerm.getSort());
		final Object value = constTerm.getValue();
		if (SmtSortUtils.isIntSort(constTerm.getSort())) {
			if (value instanceof BigInteger) {
				return Rational.valueOf((BigInteger) value, BigInteger.ONE);
			}
			if (value instanceof Rational) {
				return (Rational) value;
			}
		} else if (SmtSortUtils.isRealSort(constTerm.getSort())) {
			if (value instanceof BigDecimal) {
				return toRational((BigDecimal) value);
			}
			if (value instanceof Rational) {
				return (Rational) value;
			}
			if (value instanceof BigInteger) {
				return toRational((BigInteger) value);
			}
		}
		throw new UnsupportedOperationException("Cannot convert " + constTerm.toStringDirect() + " to Rational");
	}

	/**
	 * @return true iff tv does not occur in appTerm, or appTerm has two parameters, tv is the left parameter and tv
	 *         does not occur in the right prarameter.
	 */
	public static boolean occursAtMostAsLhs(final TermVariable tv, final ApplicationTerm appTerm) {
		if (appTerm.getParameters().length != 2) {
			return !Arrays.asList(appTerm.getFreeVars()).contains(tv);
		}
		if (Arrays.asList(appTerm.getParameters()[1].getFreeVars()).contains(tv)) {
			// occurs on rhs
			return false;
		}
		if (appTerm.getParameters()[0].equals(tv)) {
			return true;
		}
		return !Arrays.asList(appTerm.getParameters()[0].getFreeVars()).contains(tv);
	}

	/**
	 * Returns a quantified formula with the following two optimizations.
	 * <ul>
	 * <li>Nested quantified formulas that have the same quantifier are merged.
	 * <li>Quantified variables that do not occur in the subformula are dropped.
	 * </ul>
	 * The order of the quantified variables is preserved. If quantified formulas are merged, the variables of the outer
	 * formula come before the variables of the inner formula.
	 */
	public static Term quantifier(final Script script, final int quantifier, final Collection<TermVariable> vars,
			final Term subformula) {
		final LinkedHashMap<String, TermVariable> varMap = new LinkedHashMap<>();
		Term currentSubformula = subformula;
		Set<TermVariable> freeVarsOfCurrentSubformula =
				Arrays.stream(currentSubformula.getFreeVars()).collect(Collectors.toSet());
		vars.stream().filter(freeVarsOfCurrentSubformula::contains).forEach(x -> varMap.put(x.getName(), x));
		while (currentSubformula instanceof QuantifiedFormula
				&& ((QuantifiedFormula) currentSubformula).getQuantifier() == quantifier) {
			final QuantifiedFormula qf = (QuantifiedFormula) currentSubformula;
			currentSubformula = qf.getSubformula();
			freeVarsOfCurrentSubformula = Arrays.stream(currentSubformula.getFreeVars()).collect(Collectors.toSet());
			Arrays.stream(qf.getVariables()).filter(freeVarsOfCurrentSubformula::contains)
					.forEach(x -> varMap.put(x.getName(), x));

		}
		if (varMap.isEmpty()) {
			return subformula;
		}
		final TermVariable[] resultVars = varMap.entrySet().stream().map(Entry::getValue).toArray(TermVariable[]::new);
		return script.quantifier(quantifier, resultVars, currentSubformula);
	}

	/**
	 * Returns a new {@link Set} that contains all variables that are contained in vars and occur freely in term.
	 */
	public static List<TermVariable> projectToFreeVars(final List<TermVariable> vars, final Term term) {
		final Set<TermVariable> freeVars = Arrays.stream(term.getFreeVars()).collect(Collectors.toSet());
		final List<TermVariable> result = vars.stream().filter(freeVars::contains).collect(Collectors.toList());
		return result;
	}

	/**
	 * Returns a new {@link Set} that contains all variables that are contained in vars and occur freely in term.
	 */
	public static Set<TermVariable> projectToFreeVars(final Set<TermVariable> vars, final Term term) {
		final HashSet<TermVariable> result = new HashSet<>();
		for (final TermVariable tv : Arrays.asList(term.getFreeVars())) {
			if (vars.contains(tv)) {
				result.add(tv);
			}
		}
		return result;
	}

	/**
	 * If term is QuantifiedFormula whose quantifier is quant we return term as QuantifiedFormula otherwise we return
	 * null;
	 */
	public static QuantifiedFormula isQuantifiedFormulaWithSameQuantifier(final int quant, final Term term) {
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			if (quant == quantifiedFormula.getQuantifier()) {
				return quantifiedFormula;
			}
		}
		return null;
	}

	/**
	 * @return true iff term is {@link ApplicationTerm} with functionName.
	 */
	public static boolean isFunctionApplication(final Term term, final String functionName) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol fun = ((ApplicationTerm) term).getFunction();
			if (fun.getName().equals(functionName)) {
				return true;
			}
		}
		return false;
	}

	public static ApplicationTerm getFunctionApplication(final Term term, final String functionName) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals(functionName)) {
				return appTerm;
			}
		}
		return null;
	}

	/**
	 * @return true iff term is a div from the theory of Ints
	 */
	public static boolean isIntDiv(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}
		final FunctionSymbol fun = ((ApplicationTerm) term).getFunction();
		if (fun.isIntern()) {
			return ((ApplicationTerm) term).getFunction().getName().equals("div");
		}
		return false;
	}

	/**
	 *
	 * @return true iff term is a mod from the theory of Ints
	 */
	public static boolean isIntMod(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}
		final FunctionSymbol fun = ((ApplicationTerm) term).getFunction();
		if (fun.isIntern()) {
			return ((ApplicationTerm) term).getFunction().getName().equals("mod");
		}
		return false;
	}

	/**
	 * @return logically equivalent term in disjunctive normal form (DNF)
	 */
	// TODO: xnfConversionTechnique is currently not used, should we remove it?
	public static Term toDnf(final IUltimateServiceProvider services, final ManagedScript mgdScript, final Term term,
			final XnfConversionTechnique xnfConversionTechnique) {
		return new DnfTransformer(mgdScript, services).transform(term);
	}

	/**
	 * @return logically equivalent term in negation normal form (NNF)
	 */
	public static Term toNnf(final IUltimateServiceProvider services, final ManagedScript mgdScript, final Term term) {
		return new NnfTransformer(mgdScript, services, QuantifierHandling.PULL).transform(term);
	}

	/**
	 * @return logically equivalent term in conjunctive normal form (CNF)
	 */
	// TODO: xnfConversionTechnique is currently not used, should we remove it?
	public static Term toCnf(final IUltimateServiceProvider services, final ManagedScript mgdScript, final Term term,
			final XnfConversionTechnique xnfConversionTechnique) {
		return new CnfTransformer(mgdScript, services).transform(term);
	}

	/**
	 * Returns true for {@link Sorts} for which we can obtain values. E.g. for arrays we cannot get values that our
	 * analysis can process, since arrays are infinite in general. However, if the range Sort of an array is bitvector
	 * sort we can get values for array cells (resp. the corresponding select term).
	 */
	public static boolean isSortForWhichWeCanGetValues(final Sort sort) {
		return SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBoolSort(sort) || SmtSortUtils.isBitvecSort(sort)
				|| SmtSortUtils.isFloatingpointSort(sort);
	}

	/**
	 * Get values from script and transform them try to simplify them.
	 *
	 * @param script
	 *            Script that is in a state where it can provide values, e.g., after a check-sat where the response was
	 *            sat.
	 * @param terms
	 *            Collection of term for which we want to have possible values in the current satisfying model
	 * @return Mapping that maps to each term for which we want a value a possible value in the current satisfying
	 *         model.
	 */
	public static Map<Term, Term> getValues(final Script script, final Collection<Term> terms) {
		if (terms.isEmpty()) {
			return Collections.emptyMap();
		}
		final Term[] asArray = terms.toArray(new Term[terms.size()]);
		final Map<Term, Term> mapFromSolver = script.getValue(asArray);
		/*
		 * Some solvers, e.g., Z3 return -1 not as a literal but as a unary minus of a positive literal. We use our
		 * affine term to obtain the negative literal.
		 */
		final Map<Term, Term> copyWithNiceValues = new HashMap<>();
		for (final Entry<Term, Term> entry : mapFromSolver.entrySet()) {
			copyWithNiceValues.put(entry.getKey(), makeAffineIfPossible(script, entry.getValue()));
		}
		return Collections.unmodifiableMap(copyWithNiceValues);
	}

	private static Term makeAffineIfPossible(final Script script, final Term term) {
		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(script).transform(term);
		if (affineTerm.isErrorTerm()) {
			return term;
		}
		return affineTerm.toTerm(script);
	}

	public static Term constructPositiveNormalForm(final Script script, final Term term) {
		final Term result = new AffineSubtermNormalizer(script).transform(term);
		assert Util.checkSat(script, script.term("distinct", term, result)) != LBool.SAT;
		return result;
	}

	/**
	 * @return the dual quantifier: - existential if input is universal, and - universal if input is existential
	 */
	public static int getOtherQuantifier(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return QuantifiedFormula.FORALL;
		}
		if (quantifier == QuantifiedFormula.FORALL) {
			return QuantifiedFormula.EXISTS;
		}
		throw new AssertionError("unknown quantifier");
	}

	/**
	 * @return "or" if input is existential quantifier and "and" if input is universal quantifier
	 */
	public static String getCorrespondingFiniteConnective(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return "or";
		}
		if (quantifier == QuantifiedFormula.FORALL) {
			return "and";
		}
		throw new AssertionError("unknown quantifier");
	}

	/**
	 * This is an (the) alternative to script.numeral that constructs an integer constant that respects the
	 * UltimateNormalForm. See {@link UltimateNormalFormUtils}.
	 */
	public static Term constructIntValue(final Script script, final BigInteger number) {
		return Rational.valueOf(number, BigInteger.ONE).toTerm(SmtSortUtils.getIntSort(script));
	}

	/**
	 * Constructs integer values for different sorts.
	 */
	public static Term constructIntegerValue(final Script script, final Sort sort, final BigInteger integer) {
		if (SmtSortUtils.isIntSort(sort)) {
			return SmtUtils.constructIntValue(script, integer);
		}
		if (SmtSortUtils.isRealSort(sort)) {
			return script.decimal(new BigDecimal(integer));
		}
		if (SmtSortUtils.isBitvecSort(sort)) {
			return BitvectorUtils.constructTerm(script, integer, sort);
		}
		throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
	}

	/**
	 * Returns a filtered Term of {@code formula} w.r.t to the given {@code variables}. This means, all conjuncts of
	 * {@code formula}, that do not contain any of {@code variables} are discarded and the other ones returned.
	 */
	public static Term filterFormula(final Term formula, final Set<TermVariable> variables, final Script script) {
		final Term[] oldConjuncts = getConjuncts(formula);
		final List<Term> newConjuncts = new ArrayList<>(oldConjuncts.length);
		for (final Term c : oldConjuncts) {
			final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(c.getFreeVars()));
			if (DataStructureUtils.haveNonEmptyIntersection(freeVars, variables)) {
				newConjuncts.add(c);
			}
		}
		return and(script, newConjuncts);
	}

	/**
	 * Returns true iff the boolean formulas formula1 and formula2 are equivalent w.r.t script.
	 */
	public static boolean areFormulasEquivalent(final Term formula1, final Term formula2, final Script script) {
		return checkEquivalence(formula1, formula2, script) == LBool.UNSAT;
	}

	/**
	 * @return LBool.UNSAT if SMT solver was able to prove that both formulas are equivalent, LBool.SAT if SMT solver
	 *         was able to prove that both formulas are not equivalent, and LBool.UNKNOWN otherwise.
	 */
	public static LBool checkEquivalence(final Term formula1, final Term formula2, final Script script) {
		final Term notEq = script.term("distinct", formula1, formula2);
		return Util.checkSat(script, notEq);
	}

	/**
	 * @return LBool.UNSAT if the SMT solver was able to prove that the antecedent
	 *         implies the succedent, LBool.SAT if the SMT was able to prove that
	 *         the antecent does not imply the succedent, and LBool.UNKNOWN
	 *         otherwise.
	 */
	public static LBool checkImplication(final Term antecedent, final Term succedent, final Script script) {
		final Term notImply = SmtUtils.and(script, antecedent, SmtUtils.not(script, succedent));
		return Util.checkSat(script, notImply);
	}

	/**
	 * Returns true iff the boolean formulas formula1 and formula2 are equivalent under the given assumption w.r.t
	 * script.
	 */
	public static LBool checkEquivalenceUnderAssumption(final Term formula1, final Term formula2, final Term assumption,
			final Script script) {
		final Term eq = binaryEquality(script, formula1, formula2);
		final Term impl = implies(script, assumption, eq);
		return Util.checkSat(script, not(script, impl));
	}

	public static void checkLogicalEquivalenceForDebugging(final Script script, final Term result, final Term input,
			final Class<?> checkedClass, final boolean tolerateUnknown) {
		script.echo(new QuotedObject(String.format("Start correctness check for %s.", checkedClass.getSimpleName())));
		final LBool lbool = SmtUtils.checkEquivalence(result, input, script);
		script.echo(new QuotedObject(
				String.format("Finished correctness check for %s. Result: " + lbool, checkedClass.getSimpleName())));
		final String errorMessage;
		switch (lbool) {
		case SAT:
			errorMessage = String.format("%s: Not equivalent to expected result: %s Input: %s",
					checkedClass.getSimpleName(), result, input);
			break;
		case UNKNOWN:
			errorMessage = String.format(
					"%s: Insufficient ressources for checking equivalence to expected result: %s Input: %s",
					checkedClass.getSimpleName(), result, input);
			break;
		case UNSAT:
			errorMessage = null;
			break;
		default:
			throw new AssertionError("unknown value " + lbool);
		}
		if (lbool == LBool.SAT || !tolerateUnknown && lbool == LBool.UNKNOWN) {
			throw new AssertionError(errorMessage);
		}
	}

	/**
	 * Returns true iff the boolean formulas formula1 and formula2 are equivalent under the given assumption w.r.t
	 * script.
	 */
	public static boolean areFormulasEquivalent(final Term formula1, final Term formula2, final Term assumption,
			final Script script) {
		final Term eq = binaryEquality(script, formula1, formula2);
		final Term impl = implies(script, assumption, eq);
		return Util.checkSat(script, not(script, impl)) == LBool.UNSAT;
	}

	/**
	 * Returns the dimension of an arraySort (0 otherwise).
	 */
	public static int getDimension(Sort sort) {
		int i = 0;
		while (sort.isArraySort()) {
			sort = sort.getArguments()[1];
			i++;
		}
		return i;
	}

	/**
	 * Tries to compute an interpolant I for the term (and first second) by first checking if the term is indeed unsat
	 * and then retrieving the interpolants.
	 *
	 * @return A pair containing the result of the {@link Script#checkSat()} call as first element and as second element
	 *         the interpolant if the result was {@link LBool#UNSAT} or null.
	 */
	public static Pair<LBool, Term> interpolateBinary(final Script script, final Term first, final Term second) {
		script.push(1);
		try {
			final Term fPart = annotateAndAssert(script, first, "first");
			final Term sPart = annotateAndAssert(script, second, "second");
			final LBool checkSatResult = script.checkSat();
			switch (checkSatResult) {
			case UNSAT:
				final Term[] interpolants = script.getInterpolants(new Term[] { fPart, sPart });
				assert interpolants != null && interpolants.length == 1;
				return new Pair<>(checkSatResult, interpolants[0]);
			case SAT:
			case UNKNOWN:
			default:
				return new Pair<>(checkSatResult, null);
			}
		} finally {
			script.pop(1);
		}
	}

	/**
	 * Creates an annotated term from term and name, asserts that term and returns a term representing the name.
	 *
	 * Note: This method changes the state of the solver!
	 */
	public static Term annotateAndAssert(final Script script, final Term term, final String name) {
		assert term.getFreeVars().length == 0 : "Term has free vars";
		final Annotation annot = new Annotation(":named", name);
		final Term fAnnot = script.annotate(term, annot);
		script.assertTerm(fAnnot);
		return script.term(name);
	}

	public static Term constructNamedTerm(final Script script, final Term term, final String name) {
		final Annotation annot = new Annotation(":named", name);
		final Term result = script.annotate(term, annot);
		return result;
	}

	/**
	 * Write a line in the SMT script.
	 */
	public static QuotedObject echo(final Script script, final String message) {
		return script.echo(new QuotedObject(message));
	}

	public static boolean isUnaryNumericMinus(final FunctionSymbol function) {
		return function.isIntern() && function.getName().equals("-") && function.getParameterSorts().length == 1
				&& function.getParameterSorts()[0].isNumericSort() && function.getReturnSort().isNumericSort();
	}

	public static boolean isSubterm(final Term term, final Term subterm) {
		return new SubtermPropertyChecker(x -> x.equals(subterm)).isSatisfiedBySomeSubterm(term);
	}

	public static Rational toRational(final long val) {
		return Rational.valueOf(val, 1L);
	}

	public static Rational toRational(final int val) {
		return Rational.valueOf(val, 1L);
	}

	public static Rational toRational(final BigInteger bigInt) {
		return Rational.valueOf(bigInt, BigInteger.ONE);
	}

	public static Rational toRational(final BigDecimal bigDec) {
		Rational rat;
		if (bigDec.scale() <= 0) {
			final BigInteger num = bigDec.toBigInteger();
			rat = Rational.valueOf(num, BigInteger.ONE);
		} else {
			final BigInteger num = bigDec.unscaledValue();
			final BigInteger denom = BigInteger.TEN.pow(bigDec.scale());
			rat = Rational.valueOf(num, denom);
		}
		return rat;
	}

	/**
	 * Associative extension of {@link #gcd(Rational, Rational)}.
	 */
	public static Rational gcd(final Collection<Rational> rationals) {
		if (rationals.isEmpty()) {
			throw new IllegalArgumentException("Need at least one rational");
		}
		return rationals.stream().reduce(SmtUtils::gcd).orElseThrow();
	}

	/**
	 * Compute the greatest common divisor of two rationals with
	 *
	 * gcd( (a/b), (c/d) ) = gcd(a*d,c*b) / b * d
	 */
	public static Rational gcd(final Rational r1, final Rational r2) {
		final BigInteger numerator =
				Rational.gcd(r1.numerator().multiply(r2.denominator()), r2.numerator().multiply(r1.denominator()));
		final BigInteger denominator = r1.denominator().multiply(r2.denominator());
		return Rational.valueOf(numerator, denominator);
	}

	public static String toString(final Rational r) {
		final Optional<BigDecimal> dec = toDecimal(r);
		return dec.isPresent() ? dec.get().toPlainString() : r.toString();
	}

	public static Set<FunctionSymbol> extractNonTheoryFunctionSymbols(final Term term) {
		final Set<Term> appTerms = SubTermFinder.find(term, x -> (x instanceof ApplicationTerm), false);
		return appTerms.stream().map(x -> ((ApplicationTerm) x).getFunction()).filter(x -> !x.isIntern())
				.collect(Collectors.toSet());
	}

	/**
	 *
	 * @param onlyOutermost
	 *            if set to true we do not descend to subterms of a term that has been found
	 */
	@SuppressWarnings("unchecked")
	public static Set<ApplicationTerm> extractApplicationTerms(final String fun, final Term term,
			final boolean onlyOutermost) {
		return (Set) SubTermFinder.find(term, x -> isFunctionApplication(x, fun), onlyOutermost);
	}

	/**
	 * Find all subterms of the given term that are constants (i.e. {@link ApplicationTerm}s with zero parameters).
	 *
	 * @param restrictToNonTheoryConstants
	 *            If set to true, we omit constants that are defined by the SMT that our solver is using. E.g. for the
	 *            theory of floats, we omit roundTowardZero which is a constant that defines a certain rounding mode.
	 */
	@SuppressWarnings("unchecked")
	public static Set<ApplicationTerm> extractConstants(final Term term, final boolean restrictToNonTheoryConstants) {
		final Predicate<Term> p;
		if (restrictToNonTheoryConstants) {
			p = (x -> SmtUtils.isConstant(x) && (x instanceof ApplicationTerm)
					&& !((ApplicationTerm) x).getFunction().isIntern());
		} else {
			p = SmtUtils::isConstant;

		}
		// hack for casting a Set<Term> which contains only ApplicationTerms into a
		// Set<ApplicationTerm>
		return (Set) SubTermFinder.find(term, p, false);
	}

	/**
	 * If the term is a negated formula return the subformula of the `not` operator,
	 * otherwise return null.
	 */
	public static Term unzipNot(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().isIntern() && appTerm.getFunction().getName().equals("not")) {
				return appTerm.getParameters()[0];
			}
		}
		return null;
	}

	/**
	 * Flatten `(⊕ (⊕ x1 ... xn) y1 .. yn)` to `(⊕ x1 ... xn y1 .. yn)`. Sound is ⊕ left-associative. Warning:
	 * Flattening sometimes allow further simplifications, especially if ⊕ is commutative. These simplifications are not
	 * done if you use this method. Do not change this such that it utilizes simplifications afterwards. This might lead
	 * to nonterminating loops since this is a low-level methods that is utilized by simplifications itself.
	 */
	public static Term flattenIntoFirstArgument(final Script script, final String funcname, final Term firstParam,
			final Term... otherParams) {
		final List<Term> resultParams;
		if ((firstParam instanceof ApplicationTerm)
				&& ((ApplicationTerm) firstParam).getFunction().getApplicationString().equals(funcname)) {
			// same operator, we can flatten
			final ApplicationTerm appTerm = (ApplicationTerm) firstParam;
			resultParams = new ArrayList<>(appTerm.getParameters().length + otherParams.length);
			resultParams.addAll(Arrays.asList(appTerm.getParameters()));
			resultParams.addAll(Arrays.asList(otherParams));
		} else {
			resultParams = new ArrayList<>(otherParams.length + 1);
			resultParams.add(firstParam);
			resultParams.addAll(Arrays.asList(otherParams));
		}
		return script.term(funcname, resultParams.toArray(new Term[resultParams.size()]));
	}

	/**
	 * SMTInterpol changed its API with 2.5-554-g428a944, so we cannot pass BigInteger indices anymore, but have to
	 * convert them to strings. This function performs this conversion, until we can decide for each place which
	 * handling is better.
	 */
	public static Term oldAPITerm(final Script script, final String funName, final BigInteger[] indices,
			final Sort returnSort, final Term[] params) {
		return script.term(funName, toStringArray(indices), returnSort, params);
	}

	public static final BigInteger[] toBigIntegerArray(final String... indices) {
		if (indices == null) {
			return null;
		}
		if (indices.length == 0) {
			return EMPTY_INDICES_BI;
		}
		final BigInteger[] biIndices = new BigInteger[indices.length];
		for (int i = 0; i < indices.length; ++i) {
			biIndices[i] = new BigInteger(indices[i]);
		}
		return biIndices;
	}

	public static final String[] toStringArray(final BigInteger... indices) {
		if (indices == null) {
			return null;
		}
		if (indices.length == 0) {
			return EMPTY_INDICES;
		}
		final String[] strIndices = new String[indices.length];
		for (int i = 0; i < indices.length; ++i) {
			strIndices[i] = indices[i].toString();
		}
		return strIndices;
	}

	private static class InnerDualJunctTracker {

		private Set<Term> mInnerDualJuncts;

		public void addOuterJunct(final Term outerJunct, final String outerConnective) {
			final Term[] innerDualJuncts = QuantifierUtils
					.getDualFiniteJuncts(QuantifierUtils.getCorrespondingQuantifier(outerConnective), outerJunct);
			if (mInnerDualJuncts == null) {
				mInnerDualJuncts = new HashSet<>(Arrays.asList(innerDualJuncts));
			} else {
				mInnerDualJuncts.retainAll(Arrays.asList(innerDualJuncts));
			}
		}

		public Set<Term> getInnerDualJuncts() {
			return mInnerDualJuncts;
		}
	}

	public static double approximateAsDouble(final Rational rat) {
		return rat.numerator().doubleValue() / rat.denominator().doubleValue();
	}

	public static class ExtendedSimplificationResult {
		private final Term mSimplifiedTerm;
		private final long mSimplificationTimeNano;
		private final long mReductionOfTreeSize;
		private final double mReductionRatioInPercent;

		public ExtendedSimplificationResult(final Term simplifiedTerm, final long simplificationTimeNano,
				final long reductionOfTreeSize, final double reductionRatioPercent) {
			mSimplifiedTerm = simplifiedTerm;
			mSimplificationTimeNano = simplificationTimeNano;
			mReductionOfTreeSize = reductionOfTreeSize;
			mReductionRatioInPercent = reductionRatioPercent;
		}

		public Term getSimplifiedTerm() {
			return mSimplifiedTerm;
		}

		public long getSimplificationTimeNano() {
			return mSimplificationTimeNano;
		}

		public long getReductionOfTreeSize() {
			return mReductionOfTreeSize;
		}

		public double getReductionRatioInPercent() {
			return mReductionRatioInPercent;
		}

		public String buildSizeReductionMessage() {
			return String.format("treesize reduction %d, result has %2.1f percent of original size",
					getReductionOfTreeSize(), getReductionRatioInPercent());
		}

	}

	/**
	 * @return true iff this number is the binary representation of a bitvector whose two's complement representation is
	 *         -1 (i.e., minus one). Exclude however the special case where bitvectors have length 1 and hence -1 and 1
	 *         coincide.
	 */
	// <pre>
	// TODO #bvineq 20201017 Matthias:
	// The name of this method might be misleading.
	// </pre>
	public static boolean isBvMinusOneButNotOne(final Rational number, final Sort bvSort) {
		if (SmtSortUtils.getBitvectorLength(bvSort) == 1) {
			return false;
		}
		if (number.equals(Rational.MONE)) {
			return true;
		}
		final int vecSize = SmtSortUtils.getBitvectorLength(bvSort);
		final BigInteger minusOne = BigInteger.valueOf(2).pow(vecSize).subtract(BigInteger.ONE);
		final Rational rationalMinusOne = Rational.valueOf(minusOne, BigInteger.ONE);
		return number.equals(rationalMinusOne);
	}

	public BigInteger computeSmallestRepresentableBitvector(final Sort bv, final BvSignedness signedness) {
		return null;
	}

	public BigInteger computeLargestRepresentableBitvector(final Sort bv, final BvSignedness signedness) {
		return null;
	}

	public static boolean isAbsorbingElement(final String booleanConnective, final Term term) {
		if (booleanConnective.equals("and")) {
			return isFalseLiteral(term);
		} else if (booleanConnective.equals("or")) {
			return isTrueLiteral(term);
		} else {
			throw new AssertionError("unsupported connective " + booleanConnective);
		}
	}

	public static boolean isNeutralElement(final String booleanConnective, final Term term) {
		if (booleanConnective.equals("and")) {
			return isTrueLiteral(term);
		} else if (booleanConnective.equals("or")) {
			return isFalseLiteral(term);
		} else {
			throw new AssertionError("unsupported connective " + booleanConnective);
		}
	}

	/**
	 * Auxiliary method that replaces all free variables in a term by constant
	 * symbols (i.e., 0-ary function symbols). These constant symbols are declared
	 * in the script. <br>
	 * Use this method with caution. The constant symbols will live forever in the
	 * current stack frame, hence this method should be used in combination with
	 * push/pop in order to remove the constant symbols from the assertion stack
	 * after they are not needed any more. <br>
	 * The name for the new constant symbols are defined by the method
	 * {@link SmtUtils#termVariable2constant}).
	 */
	public static Term replaceFreeVariablesByConstants(final Script script, final Term term) {
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i = 0; i < vars.length; i++) {
			values[i] = termVariable2constant(script, vars[i]);
		}
		return new FormulaUnLet().unlet(script.let(vars, values, term));
	}

	private static Term termVariable2constant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		final Sort[] paramSorts = {};
		final Sort resultSort = tv.getSort();
		script.declareFun(name, paramSorts, resultSort);
		return script.term(name);
	}

}
