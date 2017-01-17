/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * This class represents a linear inequality without free coefficients (i.e. variables) which need to be determined during constraint solving.
 * All the coefficients are numerical (constant) values (e.g. -1, 1, 0, ..)
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class LinearPatternWithConstantCoefficients extends AbstractLinearInvariantPattern {
	private Map<IProgramVar, AffineTerm> mProgramVars2ConstantCoefficients;
	private Map<IProgramVar, Term> mProgramVars2TermVariables = null;
	private AffineTerm mConstant = null;
	private LinearInequality mLinearInequality = null;
	private String mName = null;
	private Map<Term, AffineTerm> mAuxVarsToConstantCoefficients;
	
	public LinearPatternWithConstantCoefficients(Script solver, Set<IProgramVar> variables, String prefix, boolean strict,
			Map<IProgramVar, AffineTerm> programVarsToConstantCoefficients, Map<Term, AffineTerm> auxVarsToConstantCoefficients,
			AffineTerm constant) {
		super();
		assert (variables.equals(programVarsToConstantCoefficients.keySet())) : "The given set of variables must be equal to the key-set of the map programVarsToConstantCoefficients";
		
		mFunctionGenerator = new AffineFunctionGenerator(solver, variables, prefix, true);
		mStrictInequality = strict;
		mVariablesOfThisPattern = variables;
		mProgramVars2ConstantCoefficients = programVarsToConstantCoefficients;
		mAuxVarsToConstantCoefficients = auxVarsToConstantCoefficients;
		mConstant = constant;
	}
	
	@Override
	public Collection<Term> getCoefficients() {
		return Collections.emptyList();
	}
	
	public void setName(String name) {
		mName  = name;
	}
	
	
	public LinearInequality getLinearInequality(final Map<IProgramVar, Term> map) {
		assert (map.keySet().containsAll(mVariablesOfThisPattern)) : "The given map does not contain an entry for each variable of this pattern";
		Map<IProgramVar, Term> vars2TermsForThisPattern = new HashMap<>(mVariablesOfThisPattern.size());
		for (IProgramVar var : mVariablesOfThisPattern) {
			vars2TermsForThisPattern.put(var, map.get(var));
		}
		final LinearInequality inequality = super.mFunctionGenerator.generate(vars2TermsForThisPattern, mProgramVars2ConstantCoefficients,
				mAuxVarsToConstantCoefficients);
		inequality.setStrict(super.mStrictInequality);
		inequality.add(mConstant);
		mProgramVars2TermVariables = vars2TermsForThisPattern;
		mLinearInequality = inequality;
		return inequality;
	}
	
	@Override
	public AffineFunction getAffineFunction(final Map<Term, Rational> valuation) {
		AffineFunction func = new AffineFunction();
		for (IProgramVar pv : mProgramVars2TermVariables.keySet()) {
			if (mProgramVars2ConstantCoefficients.containsKey(pv)) {
				func.put(pv, mProgramVars2ConstantCoefficients.get(pv).getConstant().numerator());
			}
		}
		func.setConstant(mConstant.getConstant().numerator());
		return func;
	}

	@Override
	public String toString() {
		if (mLinearInequality != null) {
			if (mName != null) {
				return mName + ": " + mLinearInequality.toString();
			} else {
				return mLinearInequality.toString();
			}
		}
		return super.toString();
	}
	
	
}
