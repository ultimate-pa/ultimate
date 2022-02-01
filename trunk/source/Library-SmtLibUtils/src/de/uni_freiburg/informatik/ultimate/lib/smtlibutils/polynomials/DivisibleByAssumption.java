package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.math.BigInteger;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * An assumption that represents Terms that declare something to be divisible by something else.
 * 
 * @author LeonardFichtner
 *
 */
public class DivisibleByAssumption extends AbstractAssumption{

	private final LinkedList<Term> mModTerms;
	
	public DivisibleByAssumption(final Script script, final Term dividend, final Term divisor) {
		super(script, dividend.getSort(), DivisibleByAssumption::equalZero);
		mModTerms = new LinkedList<>();
		mModTerms.add(SmtUtils.mod(script, dividend, divisor));
	}
	
	public DivisibleByAssumption(final Script script, final Sort sort, final DivisibleByAssumption... assumptions){
		super(script, sort, DivisibleByAssumption::equalZero);
		assert assumptions.length > 1 : "This constructor only makes sense for 2 or more assumptions";
		mModTerms = assumptions[0].getModTerms();
		for (int i = 1; i < assumptions.length; i++) {
			mModTerms.addAll(assumptions[i].getModTerms());
		}
	}
	
	private static Term equalZero(final Script script, final Sort sort, final Term term) {
		if(SmtSortUtils.isIntSort(sort)) {
			return equalZeroInt(script, sort, term);
		}else {
			throw new UnsupportedOperationException("This method is not implemented for this sort.");
		}
	}

	private static Term equalZeroInt(final Script script, final Sort sort, final Term term) {
		return SmtUtils.binaryEquality(script, term, SmtUtils.constructIntValue(script, BigInteger.ZERO));
	}
	
	@Override
	public boolean hasContractedForm() {
		return false;
	}
	
	@Override
	protected Term[] getConjunctsForExplicitForm() {
		final Term[] conjuncts = new Term[mModTerms.size()];
		int i = 0;
		for (final Term term : mModTerms) {
			conjuncts[i] = mRhsAppender.apply(mScript, mSort, term);
			i++;
		}
		return conjuncts;
	}
	
	@Override
	protected Term constructContractedLhs() {
		return toExplicitTerm();
	}
	
	private LinkedList<Term> getModTerms(){
		return mModTerms;
	}
}
