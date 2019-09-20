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

/**
 * A datastructure to handle the Terms that describe certain Assumptions.
 * 
 * @author LeonardFichtner
 *
 */
public class AssumptionMap {

	private Map<AssumptionForSolvability, LinkedList<Term>> mAssumptionMap;
	private Script mScript;
	
	public AssumptionMap(Script script){
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
	
	/**
	 * Get a Term, that represents all the assumptions of type "assu" so far, in explicit form,
	 * i. e. the conjunction of all assumptions.
	 * An example would be:
	 * Assumptions so far  x != 0,  y != 0
	 * Explicit form  x != 0 and y != 0
	 */
	public Term getExplicitForm(AssumptionForSolvability assu) {
		if(assu == AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT) {
			BiFunction<Script, Term, Term> eqZero = AssumptionMap::equalZeroInt;
			return constructExplicitAssumptionTerm(assu, eqZero);
		}else if (assu == AssumptionForSolvability.REAL_DIVISOR_NOT_ZERO) {
			BiFunction<Script, Term, Term> neqZero = AssumptionMap::notEqualZeroReal;
			return constructExplicitAssumptionTerm(assu, neqZero);
		}else {
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
		if(assu == AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT) {
			BiFunction<Script, Term, Term> eqZero = AssumptionMap::equalZeroInt;
			return constructContractedAssumptionTerm(assu, eqZero);
		}else if (assu == AssumptionForSolvability.REAL_DIVISOR_NOT_ZERO) {
			BiFunction<Script, Term, Term> neqZero = AssumptionMap::notEqualZeroReal;
			return constructContractedAssumptionTerm(assu, neqZero);
		}else {
			throw new UnsupportedOperationException("This method has no implementation for the given Asssumption.");
		}
	}
	
	private static Term equalZeroInt(Script script, Term term) {
		return SmtUtils.binaryEquality(script, term, SmtUtils.constructIntValue(script, BigInteger.ZERO));
	}

	private static Term notEqualZeroReal(Script script, Term term) {
		return SmtUtils.not(script, 
						    SmtUtils.binaryEquality(script, term, Rational.ZERO.toTerm(SmtSortUtils.getRealSort(script))));
	}

	private Term constructContractedAssumptionTerm(AssumptionForSolvability assu, BiFunction<Script, Term, Term> rhsConstructor) {
		LinkedList<Term> factors = mAssumptionMap.get(assu);
		Term product = SmtUtils.mul(mScript, factors.getFirst().getSort(), (Term[]) factors.toArray());
		return rhsConstructor.apply(mScript, product);
	}
	
	private Term constructExplicitAssumptionTerm(AssumptionForSolvability assu, BiFunction<Script, Term, Term> rhsConstructor) {
		LinkedList<Term> list = mAssumptionMap.get(assu);
		Term[] conjuncts = new Term[list.size()];
		int i = 0;
		for (Term term : list) {
			conjuncts[i] = rhsConstructor.apply(mScript, term);
			i++;
		}
		return SmtUtils.and(mScript, conjuncts);
	}
}
