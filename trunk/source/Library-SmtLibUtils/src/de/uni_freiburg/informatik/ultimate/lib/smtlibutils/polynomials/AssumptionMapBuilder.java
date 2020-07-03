package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation.AssumptionForSolvability;
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

	private Map<AssumptionForSolvability, IAssumption> mAssumptionMap;
	private final Script mScript;
	
	public AssumptionMapBuilder(final Script script){
		mAssumptionMap = Collections.emptyMap();
		mScript = script;
	}
	
	/**
	 * Use this method to put a DivisorNotZero-Assumption into the Map.
	 */
	public void putDivisorNotZero(final Term divisor) {
		if (SmtSortUtils.isRealSort(divisor.getSort())){
			put(AssumptionForSolvability.REAL_DIVISOR_NOT_ZERO, new VariableNotZeroAssumption(mScript, divisor),
			    AssumptionMapBuilder::castAndCreateVarNotZeroAssu);
		}else if (SmtSortUtils.isIntSort(divisor.getSort())) {
			put(AssumptionForSolvability.INTEGER_DIVISOR_NOT_ZERO, new VariableNotZeroAssumption(mScript, divisor),
				AssumptionMapBuilder::castAndCreateVarNotZeroAssu);
		}else {
			throw new UnsupportedOperationException("There is no such assumption of this sort.");
		}
	}
	
	/**
	 * Use this method to put a DivisibleByConstant-Assumption into the Map.
	 */
	public void putDivisibleByConstant(final Term dividend, final Term divisor) {
		if (SmtSortUtils.isIntSort(dividend.getSort())){
			put(AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT, 
				new DivisibleByAssumption(mScript, dividend, divisor),
				AssumptionMapBuilder::castAndCreateDivByAssu);
		}else {
			throw new UnsupportedOperationException("There is no such assumption of this sort.");
		}
	}
	
	/**
	 * Use this method to put a DivisibleByVariable-Assumption into the Map.
	 */
	public void putDivisibleByVariable(final Term dividend, final Term divisor) {
		if (SmtSortUtils.isIntSort(dividend.getSort())){
			put(AssumptionForSolvability.INTEGER_DIVISIBLE_BY_VARIABLE, 
				new DivisibleByAssumption(mScript, dividend, divisor),
				AssumptionMapBuilder::castAndCreateDivByAssu);
		}else {
			throw new UnsupportedOperationException("There is no such assumption of this sort.");
		}
	}
	
	private void put(final AssumptionForSolvability assuType, final IAssumption assu, 
					 final BiAssumptionConstructor<? extends IAssumption> assuConst) {
		if (mAssumptionMap.isEmpty()) {
			mAssumptionMap = Collections.singletonMap(assuType, assu);
		}else if (mAssumptionMap.size() == 1) {
			if (mAssumptionMap.containsKey(assuType)) {
				mAssumptionMap = Collections.singletonMap(assuType, 
													      assuConst.apply(mScript, mAssumptionMap.get(assuType), assu));
			}else {
				final Entry<AssumptionForSolvability, IAssumption> entry = mAssumptionMap.entrySet().iterator().next();
				mAssumptionMap = new HashMap<>();
				mAssumptionMap.put(entry.getKey(), entry.getValue());
				mAssumptionMap.put(assuType, assu);
			}
		}else {
			if(mAssumptionMap.containsKey(assuType)) {
				mAssumptionMap.put(assuType, assuConst.apply(mScript, mAssumptionMap.get(assuType), assu));
			}else {
				mAssumptionMap.put(assuType, assu);
			}
		}
	}
	
	private static DivisibleByAssumption castAndCreateDivByAssu(final Script script, final IAssumption assu1, final IAssumption assu2) {
		if (assu1 instanceof DivisibleByAssumption && assu2 instanceof DivisibleByAssumption) {
			final DivisibleByAssumption[] assus = new DivisibleByAssumption[2];
			assus[0] = (DivisibleByAssumption) assu1;
			assus[1] = (DivisibleByAssumption) assu2;
			return new DivisibleByAssumption(script, assu1.getSort(), assus);
		}
		throw new IllegalArgumentException("Someone has put an assumption at the wrong place");
	}
	
	private static VariableNotZeroAssumption castAndCreateVarNotZeroAssu(final Script script, 
																  		 final IAssumption assu1, 
																  		 final IAssumption assu2) {
		if (assu1 instanceof VariableNotZeroAssumption && assu2 instanceof VariableNotZeroAssumption) {
			final VariableNotZeroAssumption[] assus = new VariableNotZeroAssumption[2];
			assus[0] = (VariableNotZeroAssumption) assu1;
			assus[1] = (VariableNotZeroAssumption) assu2;
			return new VariableNotZeroAssumption(script, assu1.getSort(), assus);
		}
		throw new IllegalArgumentException("Someone has put an assumption at the wrong place");
	}
	
	public boolean hasContractedForm(final AssumptionForSolvability assu) {
		return mAssumptionMap.get(assu).hasContractedForm();
	}
	
	/**
	 * Get a Term, that represents all the assumptions of type "assu" so far, in explicit form,
	 * i. e. the conjunction of all assumptions.
	 * Returns true if no such assumptions exist.
	 * An example would be:
	 * Assumptions so far  x != 0,  y != 0
	 * Explicit form  x != 0 and y != 0
	 */
	public Term getExplicitForm(final AssumptionForSolvability assu) {
		if (mAssumptionMap.containsKey(assu)) {
			return mAssumptionMap.get(assu).toExplicitTerm();
		}
		return mScript.term("true");
	}

	/**
	 * Get a Term, that represents all the assumptions of type "assu" so far, in contracted form if possible.
	 * If the assumptions do not have such a form, the explicit form is returned.
	 * Returns true if no such assumptions exist.
	 * An example of a contracted form would be:
	 * Assumptions so far  x != 0,  y != 0
	 * Contracted form  x*y != 0
	 */
	public Term getContractedFormIfPossible(final AssumptionForSolvability assu) {
		if (mAssumptionMap.containsKey(assu)) {
			return mAssumptionMap.get(assu).toContractedTermIfPossible();
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
		final SparseMapBuilder<AssumptionForSolvability, Term> mapBuilder = new SparseMapBuilder<>();
		for (final AssumptionForSolvability assu : mAssumptionMap.keySet()) {
			mapBuilder.put(assu, getExplicitForm(assu));
		}
		return mapBuilder.getBuiltMap();
	}
	
	public Map<AssumptionForSolvability, Term> getContractedAssumptionMapWherePossible() {
		final SparseMapBuilder<AssumptionForSolvability, Term> mapBuilder = new SparseMapBuilder<>();
		for (final AssumptionForSolvability assu : mAssumptionMap.keySet()) {
			if (hasContractedForm(assu)) {
				mapBuilder.put(assu, getContractedFormIfPossible(assu));
			}else {
				mapBuilder.put(assu, getExplicitForm(assu));
			}
		}
		return mapBuilder.getBuiltMap();
	}
	
	@FunctionalInterface
	public interface BiAssumptionConstructor<S> {
		public S apply(Script script, IAssumption assu1, IAssumption assu2);
	}
}
