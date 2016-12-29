/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Collections;
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
	
	public LinearPatternWithConstantCoefficients(Script solver, Set<IProgramVar> variables, String prefix, boolean strict,
			Map<IProgramVar, AffineTerm> programVarsToConstantCoefficients, AffineTerm constant) {
		super(solver, variables, prefix, strict);
		assert (variables.equals(programVarsToConstantCoefficients.keySet())) : "The given set of variables must be equal to the key-set of the map programVarsToConstantCoefficients";
		
		super.mFunctionGenerator = new AffineFunctionGenerator(solver, variables, prefix, true);
		mProgramVars2ConstantCoefficients = programVarsToConstantCoefficients;
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
//		Map<IProgramVar, Term> completeMap = new HashMap<>();
//		completeMap.putAll(map);
//		for (Entry<IProgramVar, Term> entry : lastOccurrenceOfVars.entrySet()) {
//			if (!map.containsKey(entry.getKey())) {
//				completeMap.put(entry.getKey(), entry.getValue());
//			}
//		}
		assert (map.keySet().equals(mVariablesOfThisPattern)) : "The given map does not contain an entry for each variable of this pattern";
		final LinearInequality inequality = super.mFunctionGenerator.generate(map, mProgramVars2ConstantCoefficients);
		inequality.setStrict(super.mStrictInequality);
		inequality.add(mConstant);
		mProgramVars2TermVariables = map;
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
