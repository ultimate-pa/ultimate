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
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class SmtUtils {
	
	private SmtUtils() {
		// Prevent instantiation of this utility class
	}
	
	public static Term simplify(Script script, Term formula, IUltimateServiceProvider services) {
		Logger logger = services.getLoggingService().getLogger(ModelCheckerUtils.sPluginID);
		logger.debug(new DebugMessage(
				"simplifying formula of DAG size {0}", 
				new DagSizePrinter(formula)));
		Term simplified = (new SimplifyDDAWithTimeout(script, services)).getSimplifiedTerm(formula);
		logger.debug(new DebugMessage(
				"DAG size before simplification {0}, DAG size after simplification {1}", 
				new DagSizePrinter(formula), new DagSizePrinter(simplified)));
		return simplified;
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
	 * Takes an ApplicationTerm with pairwise function symbol (e.g. distinct) or
	 * chainable function symbol (e.g. equality) and return 
	 * a conjunction of pairwise applications of the function symbol.
	 * E.g. the ternary equality (= a b c) becomes
	 * (and (= a b) (= a c) (= b c)).
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
		for (int i=0; i<params.length; i++) {
			for (int j=i+1; j<params.length; j++) {
				conjuncts.add(script.term(functionName, params[i], params[j]));
			}
		}
		return Util.and(script, conjuncts.toArray(new Term[conjuncts.size()]));
	}
	
	public static boolean hasBooleanParams(ApplicationTerm term) {
		Term[] params = term.getParameters();
		boolean result = params[0].getSort().getName().equals("Bool");
		return result;
	}
	
	
	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is 
	 * equivalent to (= lhs rhs) but uses only the boolean connectives "and" and
	 * "or".
	 */
	public static Term binaryBooleanEquality(Script script, Term lhs, Term rhs) {
		assert lhs.getSort().getName().equals("Bool");
		assert rhs.getSort().getName().equals("Bool");
		Term bothTrue = Util.and(script, lhs, rhs);
		Term bothFalse = Util.and(script, 
				Util.not(script, lhs), 
				Util.not(script, rhs));
		return Util.or(script, bothTrue, bothFalse);
	}
	
	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is 
	 * equivalent to (not (= lhs rhs)) but uses only the boolean connectives 
	 * "and" and "or".
	 */
	public static Term binaryBooleanInequality(Script script, Term lhs, Term rhs) {
		assert lhs.getSort().getName().equals("Bool");
		assert rhs.getSort().getName().equals("Bool");
		Term oneIsTrue = Util.or(script, lhs, rhs);
		Term oneIsFalse = Util.or(script, 
				Util.not(script, lhs), 
				Util.not(script, rhs));
		return Util.and(script, oneIsTrue, oneIsFalse);
	}
	
	/**
	 * Given a list of Terms term_1, ... ,term_n returns a new list that 
	 * contains (not term_1), ... ,(not term_n) in this order.
	 */
	public static List<Term> negateElementwise(Script script, List<Term> terms) {
		List<Term> result = new ArrayList<>(terms.size());
		for (Term term : terms) {
			result.add(Util.not(script, term));
		}
		return result;
	}
	
	
	/**
	 * Returns the term that selects the element at index from (possibly) multi
	 * dimensional array a.
	 * E.g. If the array has Sort (Int -> Int -> Int) and index is [23, 42],
	 * this method returns the term ("select" ("select" a 23) 42).  
	 */
	public static Term multiDimensionalSelect(Script script, Term a, ArrayIndex index) {
		assert index.size() >= 0;
		assert a.getSort().isArraySort();
		Term result = a;
		for (int i=0; i<index.size(); i++) {
			result = script.term("select", result, index.get(i));
		}
		return result;
	}
	
	/**
	 * Returns the term that stores the element at index from (possibly) multi
	 * dimensional array a.
	 * E.g. If the array has Sort (Int -> Int -> Int) and we store the value
	 * val at index [23, 42], this method returns the term 
	 * (store a 23 (store (select a 23) 42 val)).
	 */
	public static Term multiDimensionalStore(Script script, Term a, ArrayIndex index, Term value) {
		assert index.size() > 0;
		assert a.getSort().isArraySort();
		Term result = value;
		for (int i=index.size()-1; i>=0; i--) {
			Term selectUpToI = multiDimensionalSelect(script, a, index.getFirst(i));
			result = script.term("store", selectUpToI, index.get(i), result);
		}
		return result;
	}
	
	/**
	 * Returns true iff each key and each value is non-null.
	 */
	public static <K,V> boolean neitherKeyNorValueIsNull(Map<K,V> map) {
		for (Entry<K, V> entry  : map.entrySet()) {
			if (entry.getKey() == null || entry.getValue() == null) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Given the array of terms [lhs_1, ..., lhs_n] and the array of terms 
	 * [rhs_1, ..., rhs_n], return the conjunction of the following equalities
	 * lhs_1 = rhs_1, ... , lhs_n = rhs_n.  
	 */
	public static Term pairwiseEquality(Script script, List<Term> lhs, List<Term> rhs) {
		if (lhs.size() != rhs.size()) {
			throw new IllegalArgumentException("must have same length");
		}
		Term[] equalities = new Term[lhs.size()];
		for (int i=0; i<lhs.size(); i++) {
			equalities[i] = binaryEquality(script, lhs.get(i), rhs.get(i)); 
		}
		return Util.and(script, equalities);
	}
	
	/**
	 * Construct the following term.
	 * (index1 == index2) ==> (value1 == value2)
	 * 
	 */
	public static Term indexEqualityImpliesValueEquality(Script script, 
			ArrayIndex index1, ArrayIndex index2, 
			Term value1, Term value2) {
		assert index1.size() == index2.size();
		Term indexEquality = Util.and(script, SmtUtils.pairwiseEquality(script, index1, index2));
		Term valueEquality = SmtUtils.binaryEquality(script, value1, value2);
		Term result = Util.or(script, Util.not(script, indexEquality), valueEquality);
		return result;
	}
	
	
	/**
	 * Return term that represents the sum of all summands. Return the neutral
	 * element for sort sort if summands is empty.
	 */
	public static Term sum(Script script, Sort sort, Term... summands) {
		assert sort.isNumericSort();
		if (summands.length == 0) {
			if (sort.toString().equals("Int")) {
				return script.numeral(BigInteger.ZERO);
			} else if (sort.toString().equals("Real")) {
				return script.decimal(BigDecimal.ZERO);
			} else {
				throw new UnsupportedOperationException("unkown sort " + sort);
			}
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			return script.term("+", summands);
		}
	}
	
	/**
	 * Returns the equality ("=" lhs rhs), or true resp. false if some simple
	 * checks detect validity or unsatisfiablity of the equality.
	 */
	public static Term binaryEquality(Script script, Term lhs, Term rhs) {
		if (lhs == rhs) {
			return script.term("true");
		} else if (twoConstantTermsWithDifferentValue(lhs, rhs)) {
			return script.term("false");
		} else {
			return script.term("=", lhs, rhs);
		}
	}
	
	
	
	/**
	 * Returns true iff. fst and snd are different literals of the same numeric
	 * sort ("Int" or "Real").
	 * @exception Throws UnsupportedOperationException if both arguments do not
	 * have the same Sort.
	 */
	private static boolean twoConstantTermsWithDifferentValue(Term fst, Term snd) {
		if (!fst.getSort().equals(snd.getSort())) {
			throw new UnsupportedOperationException("arguments sort different");
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
		for (int i=0; i<subtituents.size(); i++) {
			result.add(subst.transform(subtituents.get(i)));
		}
		return result;
	}
	
	/**
	 * Removes vertical bars from a String.
	 * In SMT-LIB identifiers can be quoted using | (vertical bar) and  
	 * vertical bars must not be nested.
	 */
	public static String removeSmtQuoteCharacters(String string) {
		String result = string.replaceAll("\\|", ""); 
		return result;
	}
	
	public static Map<Term, Term> termVariables2Constants(Script script, 
			VariableManager variableManager, Collection<TermVariable> termVariables) {
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
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select", true)).findMatchingSubterms(term);
		result = result && selectTerms.isEmpty();
		Set<ApplicationTerm> storeTerms = 
				(new ApplicationTermFinder("store", true)).findMatchingSubterms(term);
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
	
	/**
	 * A constant is an ApplicationTerm with zero parameters whose function
	 * symbol is not intern.
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
}
