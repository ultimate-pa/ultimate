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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class SmtUtils {

	private SmtUtils() {
		// Prevent instantiation of this utility class
	}

	public static Term simplify(Script script, Term formula, IUltimateServiceProvider services) {
		Logger logger = services.getLoggingService().getLogger(ModelCheckerUtils.sPluginID);
		logger.debug(new DebugMessage("simplifying formula of DAG size {0}", new DagSizePrinter(formula)));
		Term simplified = (new SimplifyDDAWithTimeout(script, services)).getSimplifiedTerm(formula);
		logger.debug(new DebugMessage("DAG size before simplification {0}, DAG size after simplification {1}",
				new DagSizePrinter(formula), new DagSizePrinter(simplified)));
		return simplified;
	}

	public static LBool checkSatTerm(Script script, Term formula) {
		return Util.checkSat(script, formula);
	}

	/**
	 * If term is a conjunction return all conjuncts, otherwise return term.
	 */
	public static Term[] getConjuncts(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("and")) {
				return appTerm.getParameters();
			}
		}
		Term[] result = new Term[1];
		result[0] = term;
		return result;
	}

	/**
	 * If term is a disjunction return all disjuncts, otherwise return term.
	 */
	public static Term[] getDisjuncts(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("or")) {
				return appTerm.getParameters();
			}
		}
		Term[] result = new Term[1];
		result[0] = term;
		return result;
	}

	/**
	 * Takes an ApplicationTerm with pairwise function symbol (e.g. distinct) or chainable function symbol (e.g.
	 * equality) and return a conjunction of pairwise applications of the function symbol. E.g. the ternary equality (=
	 * a b c) becomes (and (= a b) (= a c) (= b c)).
	 */
	public static Term binarize(Script script, ApplicationTerm term) {
		FunctionSymbol functionSymbol = term.getFunction();
		if (!functionSymbol.isPairwise() && !functionSymbol.isChainable()) {
			throw new IllegalArgumentException("can only binarize pairwise terms");
		}
		String functionName = functionSymbol.getApplicationString();
		Term[] params = term.getParameters();
		assert params.length > 1;
		List<Term> conjuncts = new ArrayList<Term>();
		for (int i = 0; i < params.length; i++) {
			for (int j = i + 1; j < params.length; j++) {
				conjuncts.add(script.term(functionName, params[i], params[j]));
			}
		}
		return Util.and(script, conjuncts.toArray(new Term[conjuncts.size()]));
	}

	public static boolean firstParamIsBool(ApplicationTerm term) {
		Term[] params = term.getParameters();
		boolean result = params[0].getSort().getName().equals("Bool");
		return result;
	}

	public static boolean allParamsAreBool(ApplicationTerm term) {
		for (Term param : term.getParameters()) {
			if (!param.getSort().getName().equals("Bool")) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is equivalent to (= lhs rhs) but uses only the
	 * boolean connectives "and" and "or".
	 */
	public static Term binaryBooleanEquality(Script script, Term lhs, Term rhs) {
		assert lhs.getSort().getName().equals("Bool");
		assert rhs.getSort().getName().equals("Bool");
		Term bothTrue = Util.and(script, lhs, rhs);
		Term bothFalse = Util.and(script, Util.not(script, lhs), Util.not(script, rhs));
		return Util.or(script, bothTrue, bothFalse);
	}

	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is equivalent to (not (= lhs rhs)) but uses only
	 * the boolean connectives "and" and "or".
	 */
	public static Term binaryBooleanNotEquals(Script script, Term lhs, Term rhs) {
		assert lhs.getSort().getName().equals("Bool");
		assert rhs.getSort().getName().equals("Bool");
		Term oneIsTrue = Util.or(script, lhs, rhs);
		Term oneIsFalse = Util.or(script, Util.not(script, lhs), Util.not(script, rhs));
		return Util.and(script, oneIsTrue, oneIsFalse);
	}

	/**
	 * Given a list of Terms term_1, ... ,term_n returns a new list that contains (not term_1), ... ,(not term_n) in
	 * this order.
	 */
	public static List<Term> negateElementwise(Script script, List<Term> terms) {
		List<Term> result = new ArrayList<>(terms.size());
		for (Term term : terms) {
			result.add(Util.not(script, term));
		}
		return result;
	}

	/**
	 * Returns the term that selects the element at index from (possibly) multi dimensional array a. E.g. If the array
	 * has Sort (Int -> Int -> Int) and index is [23, 42], this method returns the term ("select" ("select" a 23) 42).
	 */
	public static Term multiDimensionalSelect(Script script, Term a, ArrayIndex index) {
		assert a.getSort().isArraySort();
		Term result = a;
		for (int i = 0; i < index.size(); i++) {
			result = script.term("select", result, index.get(i));
		}
		return result;
	}

	/**
	 * Returns the term that stores the element at index from (possibly) multi dimensional array a. E.g. If the array
	 * has Sort (Int -> Int -> Int) and we store the value val at index [23, 42], this method returns the term (store a
	 * 23 (store (select a 23) 42 val)).
	 */
	public static Term multiDimensionalStore(Script script, Term a, ArrayIndex index, Term value) {
		assert index.size() > 0;
		assert a.getSort().isArraySort();
		Term result = value;
		for (int i = index.size() - 1; i >= 0; i--) {
			Term selectUpToI = multiDimensionalSelect(script, a, index.getFirst(i));
			result = script.term("store", selectUpToI, index.get(i), result);
		}
		return result;
	}

	/**
	 * Returns true iff each key and each value is non-null.
	 */
	public static <K, V> boolean neitherKeyNorValueIsNull(Map<K, V> map) {
		for (Entry<K, V> entry : map.entrySet()) {
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
	public static Term pairwiseEquality(Script script, List<Term> lhs, List<Term> rhs) {
		if (lhs.size() != rhs.size()) {
			throw new IllegalArgumentException("must have same length");
		}
		Term[] equalities = new Term[lhs.size()];
		for (int i = 0; i < lhs.size(); i++) {
			equalities[i] = binaryEquality(script, lhs.get(i), rhs.get(i));
		}
		return Util.and(script, equalities);
	}

	/**
	 * Construct the following term. (index1 == index2) ==> (value1 == value2)
	 * 
	 */
	public static Term indexEqualityImpliesValueEquality(Script script, ArrayIndex index1, ArrayIndex index2,
			Term value1, Term value2) {
		assert index1.size() == index2.size();
		Term indexEquality = Util.and(script, SmtUtils.pairwiseEquality(script, index1, index2));
		Term valueEquality = SmtUtils.binaryEquality(script, value1, value2);
		Term result = Util.or(script, Util.not(script, indexEquality), valueEquality);
		return result;
	}

	/**
	 * Return term that represents the sum of all summands. Return the neutral element for sort sort if summands is
	 * empty.
	 */
	public static Term sum(Script script, Sort sort, Term... summands) {
		assert sort.isNumericSort() || BitvectorUtils.isBitvectorSort(sort);
		if (summands.length == 0) {
			if (sort.toString().equals("Int")) {
				return script.numeral(BigInteger.ZERO);
			} else if (sort.toString().equals("Real")) {
				return script.decimal(BigDecimal.ZERO);
			} else if (BitvectorUtils.isBitvectorSort(sort)) {
				return BitvectorUtils.constructTerm(script, BigInteger.ZERO, sort);
			} else {
				throw new UnsupportedOperationException("unkown sort " + sort);
			}
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			if (sort.isNumericSort()) {
				return script.term("+", summands);
			} else if (BitvectorUtils.isBitvectorSort(sort)) {
				return script.term("bvadd", summands);
			} else {
				throw new UnsupportedOperationException("unkown sort " + sort);
			}
		}
	}

	/**
	 * Return term that represents the product of all factors. Return the neutral element for sort sort if factors is
	 * empty.
	 */
	public static Term mul(Script script, Sort sort, Term... factors) {
		assert sort.isNumericSort() || BitvectorUtils.isBitvectorSort(sort);
		if (factors.length == 0) {
			if (sort.toString().equals("Int")) {
				return script.numeral(BigInteger.ONE);
			} else if (sort.toString().equals("Real")) {
				return script.decimal(BigDecimal.ONE);
			} else if (BitvectorUtils.isBitvectorSort(sort)) {
				return BitvectorUtils.constructTerm(script, BigInteger.ONE, sort);
			} else {
				throw new UnsupportedOperationException("unkown sort " + sort);
			}
		} else if (factors.length == 1) {
			return factors[0];
		} else {
			if (sort.isNumericSort()) {
				return script.term("*", factors);
			} else if (BitvectorUtils.isBitvectorSort(sort)) {
				return script.term("bvmul", factors);
			} else {
				throw new UnsupportedOperationException("unkown sort " + sort);
			}
		}
	}

	/**
	 * Return sum, in affine representation if possible.
	 * 
	 * @param funcname
	 *            either "+" or "bvadd".
	 */
	public static Term sum(Script script, String funcname, Term... summands) {
		assert funcname.equals("+") || funcname.equals("bvadd");
		final Term sum = script.term(funcname, summands);
		final AffineTerm affine = (AffineTerm) (new AffineTermTransformer(script)).transform(sum);
		if (affine.isErrorTerm()) {
			return sum;
		} else {
			return affine.toTerm(script);
		}
	}

	/**
	 * Return term that represents negation (unary minus).
	 */
	public static Term neg(Script script, Sort sort, Term operand) {
		assert sort.isNumericSort() || BitvectorUtils.isBitvectorSort(sort);
		if (sort.isNumericSort()) {
			return script.term("-", operand);
		} else if (BitvectorUtils.isBitvectorSort(sort)) {
			return script.term("bvneg", operand);
		} else {
			throw new UnsupportedOperationException("unkown sort " + sort);
		}
	}

	/**
	 * Returns the equality ("=" lhs rhs), or true resp. false if some simple checks detect validity or unsatisfiablity
	 * of the equality.
	 */
	public static Term binaryEquality(Script script, Term lhs, Term rhs) {
		if (lhs == rhs) {
			return script.term("true");
		} else if (twoConstantTermsWithDifferentValue(lhs, rhs)) {
			return script.term("false");
		} else if (lhs.getSort().getName().equals("Bool")) {
			return booleanEquality(script, lhs, rhs);
		} else {
			return script.term("=", lhs, rhs);
		}
	}

	/**
	 * Returns the equality ("=" lhs rhs), but checks if one of the arguments is true/false and simplifies accordingly.
	 */
	private static Term booleanEquality(Script script, Term lhs, Term rhs) {
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		if (lhs.equals(trueTerm)) {
			return rhs;
		} else if (lhs.equals(falseTerm)) {
			return Util.not(script, rhs);
		} else if (rhs.equals(trueTerm)) {
			return lhs;
		} else if (rhs.equals(falseTerm)) {
			return Util.not(script, lhs);
		} else {
			return script.term("=", lhs, rhs);
		}
	}

	/**
	 * Returns true iff. fst and snd are different literals of the same numeric sort ("Int" or "Real").
	 * 
	 * @exception Throws
	 *                UnsupportedOperationException if both arguments do not have the same Sort.
	 */
	private static boolean twoConstantTermsWithDifferentValue(Term fst, Term snd) {
		if (!fst.getSort().equals(snd.getSort())) {
			throw new UnsupportedOperationException("arguments sort different");
		}
		BitvectorConstant fstbw = BitvectorUtils.constructBitvectorConstant(fst);
		if (fstbw != null) {
			BitvectorConstant sndbw = BitvectorUtils.constructBitvectorConstant(snd);
			if (sndbw != null) {
				return !fstbw.equals(sndbw);
			}
		}
		if (!(fst instanceof ConstantTerm)) {
			return false;
		}
		if (!(snd instanceof ConstantTerm)) {
			return false;
		}
		if (!fst.getSort().isNumericSort()) {
			return false;
		}
		ConstantTerm fstConst = (ConstantTerm) fst;
		ConstantTerm sndConst = (ConstantTerm) snd;
		Object fstValue = fstConst.getValue();
		Object sndValue = sndConst.getValue();
		if (fstValue.getClass() != sndValue.getClass()) {
			return false;
		}
		return !fstConst.getValue().equals(sndConst.getValue());
	}

	public static List<Term> substitutionElementwise(List<Term> subtituents, SafeSubstitution subst) {
		List<Term> result = new ArrayList<Term>();
		for (int i = 0; i < subtituents.size(); i++) {
			result.add(subst.transform(subtituents.get(i)));
		}
		return result;
	}

	/**
	 * Removes vertical bars from a String. In SMT-LIB identifiers can be quoted using | (vertical bar) and vertical
	 * bars must not be nested.
	 */
	public static String removeSmtQuoteCharacters(String string) {
		String result = string.replaceAll("\\|", "");
		return result;
	}

	public static Map<Term, Term> termVariables2Constants(Script script, VariableManager variableManager,
			Collection<TermVariable> termVariables) {
		Map<Term, Term> mapping = new HashMap<Term, Term>();
		for (TermVariable tv : termVariables) {
			Term constant = variableManager.getCorrespondingConstant(tv);
			if (constant == null) {
				constant = termVariable2constant(script, tv);
			}
			mapping.put(tv, constant);
		}
		return mapping;
	}

	public static Term termVariable2constant(Script script, TermVariable tv) {
		String name = removeSmtQuoteCharacters(tv.getName());
		Sort resultSort = tv.getSort();
		script.declareFun(name, new Sort[0], resultSort);
		return script.term(name);
	}

	public static boolean containsArrayVariables(Term... terms) {
		for (Term term : terms) {
			for (TermVariable tv : term.getFreeVars()) {
				if (tv.getSort().isArraySort()) {
					return true;
				}
			}
		}
		return false;
	}

	public static boolean isArrayFree(Term term) {
		boolean result = !containsArrayVariables(term);
		Set<ApplicationTerm> selectTerms = (new ApplicationTermFinder("select", true)).findMatchingSubterms(term);
		result = result && selectTerms.isEmpty();
		Set<ApplicationTerm> storeTerms = (new ApplicationTermFinder("store", true)).findMatchingSubterms(term);
		result = result && storeTerms.isEmpty();
		return result;
	}

	public static boolean isFalse(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol fun = appTerm.getFunction();
			return fun.getApplicationString().equals("false");
		} else {
			return false;
		}
	}

	public static boolean isTrue(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol fun = appTerm.getFunction();
			return fun.getApplicationString().equals("true");
		} else {
			return false;
		}
	}

	/**
	 * A constant is an ApplicationTerm with zero parameters whose function symbol is not intern.
	 */
	public static boolean isConstant(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			return appTerm.getParameters().length == 0 && !appTerm.getFunction().isIntern();
		} else {
			return false;
		}
	}

	/**
	 * Return all free TermVariables that occur in a set of Terms.
	 */
	public static Set<TermVariable> getFreeVars(Collection<Term> terms) {
		Set<TermVariable> freeVars = new HashSet<TermVariable>();
		for (Term term : terms) {
			freeVars.addAll(Arrays.asList(term.getFreeVars()));
		}
		return freeVars;
	}

	public static Term and(Script script, Collection<Term> terms) {
		return Util.and(script, terms.toArray(new Term[terms.size()]));
	}

	public static Term or(Script script, Collection<Term> terms) {
		return Util.or(script, terms.toArray(new Term[terms.size()]));
	}

	/**
	 * @return term that is equivalent to lhs <= rhs
	 */
	public static Term leq(Script script, Term lhs, Term rhs) {
		return script.term("<=", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs < rhs
	 */
	public static Term less(Script script, Term lhs, Term rhs) {
		return script.term("<", lhs, rhs);
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
	public static ApplicationTerm buildNewConstant(Script script, String name, String sortname) throws SMTLIBException {
		script.declareFun(name, new Sort[0], script.sort(sortname));
		return (ApplicationTerm) script.term(name);
	}

	/**
	 * Convert a BigDecimal into a Rational. Stolen from Jochen's code
	 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.
	 */
	private static Rational decimalToRational(BigDecimal d) {
		Rational rat;
		if (d.scale() <= 0) {
			BigInteger num = d.toBigInteger();
			rat = Rational.valueOf(num, BigInteger.ONE);
		} else {
			BigInteger num = d.unscaledValue();
			BigInteger denom = BigInteger.TEN.pow(d.scale());
			rat = Rational.valueOf(num, denom);
		}
		return rat;
	}

	/**
	 * Convert a constant term to Rational.
	 * 
	 * @param ct
	 *            constant term that represents a Rational
	 * @return Rational from the value of ct
	 * @throws IllegalArgumentException
	 *             if ct does not represent a Rational.
	 */
	public static Rational convertCT(ConstantTerm ct) throws IllegalArgumentException {
		if (ct.getSort().getName().equals("Real")) {
			if (ct.getValue() instanceof Rational) {
				return (Rational) ct.getValue();
			} else if (ct.getValue() instanceof BigDecimal) {
				return decimalToRational((BigDecimal) ct.getValue());
			} else {
				throw new UnsupportedOperationException("ConstantTerm's value has to be either Rational or BigDecimal");
			}
		} else if (ct.getSort().getName().equals("Int")) {
			if (ct.getValue() instanceof Rational) {
				return (Rational) ct.getValue();
			} else {
				Rational r = Rational.valueOf((BigInteger) ct.getValue(), BigInteger.ONE);
				return r;
			}
		} else {
			throw new IllegalArgumentException("Trying to convert a ConstantTerm of unknown sort." + ct);
		}
	}

	/**
	 * Construct term but simplify it using lightweight simplification techniques if applicable.
	 */
	public static Term termWithLocalSimplification(Script script, String funcname, BigInteger[] indices,
			Term... params) {
		final Term result;
		switch (funcname) {
		case "and":
			result = Util.and(script, params);
			break;
		case "or":
			result = Util.or(script, params);
			break;
		case "not":
			if (params.length != 1) {
				throw new IllegalArgumentException("no not term");
			} else {
				result = Util.not(script, params[0]);
			}
			break;
		case "=":
			if (params.length != 2) {
				throw new UnsupportedOperationException("not yet implemented");
			} else {
				result = binaryEquality(script, params[0], params[1]);
			}
			break;
		case "distinct":
			if (params.length != 2) {
				throw new UnsupportedOperationException("not yet implemented");
			} else {
				result = Util.not(script, binaryEquality(script, params[0], params[1]));
			}
			break;
		case "=>":
			result = Util.implies(script, params);
			break;
		case "ite":
			if (params.length != 3) {
				throw new IllegalArgumentException("no ite");
			} else {
				result = Util.ite(script, params[0], params[1], params[2]);
			}
			break;
		case "+":
		case "bvadd": {
			result = SmtUtils.sum(script, funcname, params);
		}
			break;
		case "div":
			if (params.length != 2) {
				throw new IllegalArgumentException("no div");
			} else {
				result = div(script, params[0], params[1]);
			}
			break;
		case "mod":
			if (params.length != 2) {
				throw new IllegalArgumentException("no mod");
			} else {
				result = mod(script, params[0], params[1]);
			}
			break;
		case "zero_extend":
		case "extract":
		case "bvsub":
		case "bvmul":
		case "bvudiv":
		case "bvurem":
		case "bvsdiv":
		case "bvsrem":
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
			result = BitvectorUtils.termWithLocalSimplification(script, funcname, indices, params);
			break;
		default:
			// if (BitvectorUtils.allTermsAreBitvectorConstants(params)) {
			// throw new AssertionError("wasted optimization " + funcname);
			// }
			result = script.term(funcname, indices, null, params);
			break;
		}
		return result;
	}

	/**
	 * Returns a possibly simplified version of the Term (div dividend divisor). If dividend and divisor are both
	 * literals the returned Term is a literal which is equivalent to the result of the operation
	 */
	public static Term div(Script script, Term dividend, Term divisor) {
		if ((dividend instanceof ConstantTerm) && dividend.getSort().isNumericSort()
				&& (divisor instanceof ConstantTerm) && divisor.getSort().isNumericSort()) {
			Rational dividentAsRational = convertConstantTermToRational((ConstantTerm) dividend);
			Rational divisorAsRational = convertConstantTermToRational((ConstantTerm) divisor);
			Rational quotientAsRational = dividentAsRational.div(divisorAsRational);
			Rational result;
			if (divisorAsRational.isNegative()) {
				result = quotientAsRational.ceil();
			} else {
				result = quotientAsRational.floor();
			}
			return result.toTerm(dividend.getSort());
		} else {
			return script.term("div", dividend, divisor);
		}
	}

	/**
	 * Returns a possibly simplified version of the Term (mod dividend divisor). If dividend and divisor are both
	 * literals the returned Term is a literal which is equivalent to the result of the operation. If only the divisor
	 * is a literal we apply modulo to all coefficients of the dividend (helpful simplification in case where
	 * coefficient becomes zero).
	 */
	public static Term mod(Script script, Term divident, Term divisor) {
		final AffineTerm affineDivident = (AffineTerm) (new AffineTermTransformer(script)).transform(divident);
		final AffineTerm affineDivisor = (AffineTerm) (new AffineTermTransformer(script)).transform(divisor);
		if (affineDivident.isErrorTerm() || affineDivisor.isErrorTerm()) {
			return script.term("mod", divident, divisor);
		}
		if (affineDivisor.isZero()) {
			// pass the problem how to deal with division by zero to the
			// subsequent analysis
			return script.term("mod", divident, divisor);
		}
		if (affineDivisor.isConstant()) {
			BigInteger bigIntDivisor = toInt(affineDivisor.getConstant());
			if (affineDivident.isConstant()) {
				BigInteger bigIntDivident = toInt(affineDivident.getConstant());
				BigInteger modulus = BoogieUtils.euclideanMod(bigIntDivident, bigIntDivisor);
				return script.numeral(modulus);
			} else {
				AffineTerm moduloApplied = AffineTerm.applyModuloToAllCoefficients(script, affineDivident,
						bigIntDivisor);
				return script.term("mod", moduloApplied.toTerm(script), affineDivisor.toTerm(script));
			}
		} else {
			return script.term("mod", affineDivident.toTerm(script), affineDivisor.toTerm(script));
		}
	}

	public static BigInteger toInt(Rational integralRational) {
		if (!integralRational.isIntegral()) {
			throw new IllegalArgumentException("divident has to be integral");
		}
		if (!integralRational.denominator().equals(BigInteger.ONE)) {
			throw new IllegalArgumentException("denominator has to be zero");
		}
		return integralRational.numerator();
	}

	public static Rational toRational(BigInteger bigInt) {
		return Rational.valueOf(bigInt, BigInteger.ONE);
	}

	public static Term rational2Term(Script script, Rational rational, Sort sort) {
		if (sort.isNumericSort()) {
			return rational.toTerm(sort);
		} else if (BitvectorUtils.isBitvectorSort(sort)) {
			if (rational.isIntegral() && rational.isRational()) {
				return BitvectorUtils.constructTerm(script, rational.numerator(), sort);
			} else {
				throw new IllegalArgumentException("unable to convert rational to bitvector if not integer");
			}
		} else {
			throw new AssertionError("unknown sort " + sort);
		}
	}

	/**
	 * Check if {@link Term} which may contain free {@link TermVariable}s is satisfiable with respect to the current
	 * assertion stack of {@link Script}. Compute unsat core if unsatisfiable. Use {@link LoggingScript} to see the
	 * input. TODO: Show values of satisfying assignment (including array access) if satisfiable.
	 * 
	 * @param term
	 *            may contain free variables
	 */
	public static LBool checkSat_DebuggingVersion(Script script, Term term) {
		script.push(1);
		try {
			TermVariable[] vars = term.getFreeVars();
			Map<Term, Term> substitutionMapping = new HashMap<>();
			for (int i = 0; i < vars.length; i++) {
				Term substituent = termVariable2PseudofreshConstant(script, vars[i]);
				substitutionMapping.put(vars[i], substituent);
			}
			Map<Term, Term> ucMapping = new HashMap<>();
			Term[] conjuncts = getConjuncts(term);
			for (int i = 0; i < conjuncts.length; i++) {
				Term conjunct = (new SafeSubstitution(script, substitutionMapping)).transform(conjuncts[i]);
				String name = "conjunct" + i;
				Annotation annot = new Annotation(":named", name);
				Term annotTerm = script.annotate(conjunct, annot);
				ucMapping.put(script.term(name), conjuncts[i]);
				script.assertTerm(annotTerm);
			}
			LBool result = script.checkSat();
			if (result == LBool.UNSAT) {
				Term[] ucTerms = script.getUnsatCore();
				for (Term ucTerm : ucTerms) {
					Term conjunct = ucMapping.get(ucTerm);
					System.out.println("in uc: " + conjunct);
				}
			}
			script.pop(1);
			return result;
		} catch (Exception e) {
			// unable to recover because assertion stack is modified
			// doing the script.pop(1) in finally block does not make sense
			// since the solver might not be able to respond this will raise
			// another Exception, and we will not see Exception e any more.
			throw new AssertionError("Exception during satisfiablity check: " + e.getMessage());
		}
	}

	private static Term termVariable2PseudofreshConstant(Script script, TermVariable tv) {
		String name = tv.getName() + "_const_" + tv.hashCode();
		Sort resultSort = tv.getSort();
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
	public static Rational convertConstantTermToRational(ConstantTerm constTerm) {
		Rational rational;
		assert constTerm.getSort().isNumericSort();
		Object value = constTerm.getValue();
		if (constTerm.getSort().getName().equals("Int")) {
			if (value instanceof BigInteger) {
				rational = Rational.valueOf((BigInteger) value, BigInteger.ONE);
			} else if (value instanceof Rational) {
				rational = (Rational) value;
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (constTerm.getSort().getName().equals("Real")) {
			if (value instanceof BigDecimal) {
				rational = decimalToRational((BigDecimal) value);
			} else if (value instanceof Rational) {
				rational = (Rational) value;
			} else {
				throw new UnsupportedOperationException();
			}
		} else {
			throw new UnsupportedOperationException();
		}
		return rational;
	}

	/**
	 * @return true iff tv does not occur in appTerm, or appTerm has two parameters, tv is the left parameter and tv
	 *         does not occur in the right prarameter.
	 */
	public static boolean occursAtMostAsLhs(TermVariable tv, ApplicationTerm appTerm) {
		if (appTerm.getParameters().length != 2) {
			return !Arrays.asList(appTerm.getFreeVars()).contains(tv);
		} else {
			if (Arrays.asList(appTerm.getParameters()[1].getFreeVars()).contains(tv)) {
				// occurs on rhs
				return false;
			} else {
				if (appTerm.getParameters()[0].equals(tv)) {
					return true;
				} else {
					return !Arrays.asList(appTerm.getParameters()[0].getFreeVars()).contains(tv);
				}
			}
		}
	}

	/**
	 * Returns quantified formula. Drops quantifiers for variables that do not occur in formula.
	 */
	public static Term quantifier(Script script, int quantifier, Collection<TermVariable> vars, Term body) {
		if (vars.size() == 0) {
			return body;
		}
		ArrayList<TermVariable> resultVars = new ArrayList<>();
		for (TermVariable tv : Arrays.asList(body.getFreeVars())) {
			if (vars.contains(tv)) {
				resultVars.add(tv);
			}
		}
		if (resultVars.isEmpty()) {
			return body;
		} else {
			return script.quantifier(quantifier, resultVars.toArray(new TermVariable[resultVars.size()]), body);
		}
	}

}
