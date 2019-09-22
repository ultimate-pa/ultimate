package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SparseMapBuilder;

/**
 * A datastructure to handle the Terms that describe certain Assumptions.
 * 
 * @author LeonardFichtner
 *
 */
public class AssumptionMapBuilder {

	private Map<AssumptionForSolvability, LinkedList<Term>> mAssumptionMap;
	private Script mScript;
	
	public AssumptionMapBuilder(Script script){
		mAssumptionMap = Collections.emptyMap();
		mScript = script;
	}
	
	/**
	 * @param term 
	 * Given any assumption so far, all are of the form ψ ▷ 0, where ▷  is equality or inequality,
	 * depending on the assumption-type and ψ is the actual individual part of each assumption.
	 * Put in ψ as the parameter for term here!
	 */
	public void put(AssumptionForSolvability assu, Term term) {
		if (mAssumptionMap.isEmpty()) {
			final LinkedList<Term> list = new LinkedList<>();
			list.add(term);
			mAssumptionMap = Collections.singletonMap(assu, list);
		}else if (!mAssumptionMap.containsKey(assu)) {
			if (mAssumptionMap.size() == 1) {
				Entry<AssumptionForSolvability, LinkedList<Term>> entry = mAssumptionMap.entrySet().iterator().next();
				mAssumptionMap = new HashMap<>();
				mAssumptionMap.put(entry.getKey(), entry.getValue());
			}else {
				final LinkedList<Term> list = new LinkedList<>();
				list.add(term);
				mAssumptionMap.put(assu, list);
			}
		}else {
			final LinkedList<Term> list = mAssumptionMap.get(assu);
			list.add(term);
		}
	}
	
	public boolean hasContractedForm(AssumptionForSolvability assu) {
		return (assu == AssumptionForSolvability.REAL_DIVISOR_NOT_ZERO 
				|| assu == AssumptionForSolvability.INTEGER_DIVISOR_NOT_ZERO);
	}
	
	/**
	 * Get a Term, that represents all the assumptions of type "assu" so far, in explicit form,
	 * i. e. the conjunction of all assumptions.
	 * An example would be:
	 * Assumptions so far  x != 0,  y != 0
	 * Explicit form  x != 0 and y != 0
	 */
	public Term getExplicitForm(AssumptionForSolvability assu) {
		BiFunction<Script, Term, Term> eqOrNeqZero;
		switch (assu) {
		case INTEGER_DIVISIBLE_BY_CONSTANT:
			eqOrNeqZero = AssumptionMapBuilder::equalZeroInt;
			return constructExplicitAssumptionTerm(assu, eqOrNeqZero);
		case INTEGER_DIVISIBLE_BY_VARIABLE:
			eqOrNeqZero = AssumptionMapBuilder::equalZeroInt;
			return constructExplicitAssumptionTerm(assu, eqOrNeqZero);
		case REAL_DIVISOR_NOT_ZERO:
			eqOrNeqZero = AssumptionMapBuilder::notEqualZeroReal;
			return constructExplicitAssumptionTerm(assu, eqOrNeqZero);
		case INTEGER_DIVISOR_NOT_ZERO:
			eqOrNeqZero = AssumptionMapBuilder::notEqualZeroInt;
			return constructExplicitAssumptionTerm(assu, eqOrNeqZero);
		default:
			throw new UnsupportedOperationException("This method has no implementation for the given Asssumption.");
		}
	}

	/**
	 * Get a Term, that represents all the assumptions of type "assu" so far, in contracted form.
	 * That means the term will be of the form ψ ▷ 0, where ▷ is equality or inequality, depending on the assumption-type
	 * and ψ is a "melding" of the stored assumptions, such that ψ ▷ 0 is equivalent to the conjunction of every individual assumption
	 * (see getExplicitForm).
	 * An example would be:
	 * Assumptions so far  x != 0,  y != 0
	 * Contracted form  x*y != 0
	 */
	public Term getContractedForm(AssumptionForSolvability assu) {
		BiFunction<Script, Term, Term> eqOrNeqZero;
		switch (assu) {
		case INTEGER_DIVISIBLE_BY_CONSTANT:
			throw new UnsupportedOperationException("This assumption has no contracted form yet.");
		case INTEGER_DIVISIBLE_BY_VARIABLE:
			throw new UnsupportedOperationException("This assumption has no contracted form yet.");
		case REAL_DIVISOR_NOT_ZERO:
			eqOrNeqZero = AssumptionMapBuilder::notEqualZeroReal;
			return constructContractedAssumptionTerm(assu, eqOrNeqZero);
		case INTEGER_DIVISOR_NOT_ZERO:
			eqOrNeqZero = AssumptionMapBuilder::notEqualZeroInt;
			return constructContractedAssumptionTerm(assu, eqOrNeqZero);
		default:
			throw new UnsupportedOperationException("This method has no implementation for the given Asssumption.");
		}
	}
	
	
	private static Term equalZeroInt(Script script, Term term) {
		return SmtUtils.binaryEquality(script, term, SmtUtils.constructIntValue(script, BigInteger.ZERO));
	}

	private static Term notEqualZeroReal(Script script, Term term) {
		return SmtUtils.not(script, 
						    SmtUtils.binaryEquality(script, term, 
						    						SmtUtils.rational2Term(script, Rational.ZERO, 
						    					  						   SmtSortUtils.getRealSort(script))));
	}
	
	private static Term notEqualZeroInt(Script script, Term term) {
		return SmtUtils.not(script, 
						    SmtUtils.binaryEquality(script, term, SmtUtils.constructIntValue(script, BigInteger.ZERO)));
	}

	private Term constructContractedAssumptionTerm(AssumptionForSolvability assu, 
												   BiFunction<Script, Term, Term> rhsConstructor) {
		if (mAssumptionMap.containsKey(assu)) {
			LinkedList<Term> factors = mAssumptionMap.get(assu);
			Term[] factorArray = new Term[factors.size()];
			int i = 0;
			for (Term term : factors) {
				factorArray[i] = term;
				i++;
			}
			Term product = SmtUtils.mul(mScript, factors.getFirst().getSort(), factorArray);
			return rhsConstructor.apply(mScript, product);
		}
		return mScript.term("true");
	}
	
	private Term constructExplicitAssumptionTerm(AssumptionForSolvability assu, 
												 BiFunction<Script, Term, Term> rhsConstructor) {
		if(mAssumptionMap.containsKey(assu)) {
			LinkedList<Term> list = mAssumptionMap.get(assu);
			Term[] conjuncts = new Term[list.size()];
			int i = 0;
			for (Term term : list) {
				conjuncts[i] = rhsConstructor.apply(mScript, term);
				i++;
			}
			return SmtUtils.and(mScript, conjuncts);
		}
		return mScript.term("true");
	}
	
	public boolean isEmpty() {
		return mAssumptionMap.isEmpty();
	}
	
	public void clear() {
		mAssumptionMap = Collections.emptyMap();
	}
	
	public Map<AssumptionForSolvability, Term> getExplicitAssumptionMap() {
		SparseMapBuilder<AssumptionForSolvability, Term> mapBuilder = new SparseMapBuilder<>();
		for (AssumptionForSolvability assu : mAssumptionMap.keySet()) {
			mapBuilder.put(assu, getExplicitForm(assu));
		}
		return mapBuilder.getBuiltMap();
	}
	
	public Map<AssumptionForSolvability, Term> getContractedAssumptionMapWherePossible() {
		SparseMapBuilder<AssumptionForSolvability, Term> mapBuilder = new SparseMapBuilder<>();
		for (AssumptionForSolvability assu : mAssumptionMap.keySet()) {
			if (hasContractedForm(assu)) {
				mapBuilder.put(assu, getContractedForm(assu));
			}else {
				mapBuilder.put(assu, getExplicitForm(assu));
			}
		}
		return mapBuilder.getBuiltMap();
	}
}
