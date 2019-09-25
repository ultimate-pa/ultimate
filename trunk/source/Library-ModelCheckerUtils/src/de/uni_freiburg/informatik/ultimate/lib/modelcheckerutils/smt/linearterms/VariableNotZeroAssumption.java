package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * An assumption that represents Terms that declare variables to be notZero.
 * 
 * @author LeonardFichtner
 *
 */
public class VariableNotZeroAssumption extends AbstractAssumption{

	private final LinkedList<Term> mVariables;
	
	public VariableNotZeroAssumption(final Sort sort, final Script script, Term variable){
		super(script, sort, VariableNotZeroAssumption::notEqualZero);
		mVariables = new LinkedList<>();
		mVariables.add(variable);
	}
	
	public VariableNotZeroAssumption(final Sort sort, final Script script, VariableNotZeroAssumption... assumptions){
		super(script, sort, VariableNotZeroAssumption::notEqualZero);
		assert assumptions.length > 1 : "This constructor only makes sense for 2 or more assumptions";
		mVariables = assumptions[0].getVariables();
		for (int i = 1; i < assumptions.length; i++) {
			mVariables.addAll(assumptions[i].getVariables());
		}
	}
	
	public static Term notEqualZero(Script script, Sort sort, Term term) {
		if (SmtSortUtils.isRealSort(sort)) {
			return notEqualZeroReal(script, term);
		}else if (SmtSortUtils.isIntSort(sort)){
			return notEqualZeroInt(script, term);
		}else {
			throw new UnsupportedOperationException("This method is not implemented for this sort.");
		}
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
	
	@Override
	public boolean hasContractedForm() {
		return true;
	}
	
	@Override
	protected Term constructContractedLhs() {
		Term[] factorArray = new Term[mVariables.size()];
		int i = 0;
		for (Term term : mVariables) {
			factorArray[i] = term;
			i++;
		}
		Term product = SmtUtils.mul(mScript, mSort, factorArray);
		return mRhsAppender.apply(mScript, mSort, product);
	}
	
	@Override
	protected Term[] getConjunctsForExplicitForm() {
		Term[] conjuncts = new Term[mVariables.size()];
		int i = 0;
		for (Term term : mVariables) {
			conjuncts[i] = mRhsAppender.apply(mScript, mSort, term);
			i++;
		}
		return conjuncts;
	}
	
	private LinkedList<Term> getVariables() {
		return mVariables;
	}
}
