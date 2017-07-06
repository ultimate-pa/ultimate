package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;

public class EqFunction implements IEqFunctionIdentifier<EqNode, EqFunction> {
	
	
	
	@Deprecated
	private IProgramVarOrConst mPvoc;

	private final Term mTerm;

	@Deprecated
	private boolean mIsVersioned;

	private final EqNodeAndFunctionFactory mFactory;

	private final int mArity;
	
	public EqFunction(Term term, EqNodeAndFunctionFactory factory) {
		mTerm = term;
		mFactory = factory;
		assert mTerm.getSort().isArraySort();
//		mArity = mTerm.getSort().getArguments().length - 1;
		mArity = new MultiDimensionalSort(mTerm.getSort()).getDimension();
	}

	public boolean isGlobal() {
		return mPvoc.isGlobal();
	}

	public String getProcedure() {
		if (isGlobal()) {
			return null;
		}
		
		if (mPvoc instanceof IProgramVar) {
			return ((IProgramVar) mPvoc).getProcedure();
		}

		assert false : "how to determine the procedure of a non-global constant?? -- if that makes sense..";
		return null;
	}



	@Override
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public EqFunction renameVariables(Map<Term, Term> substitutionMapping) {
//		final Term renamed = substitutionMapping.get(mTerm);
//		if (renamed == null) {
//			return this;
//		}
//		return mFactory.getOrConstructEqFunction(mPvoc, renamed);
		return mFactory.constructRenamedEqFunction(this, substitutionMapping);
	}

	public IProgramVarOrConst getPvoc() {
		return mPvoc;
	}

	public String getFunctionName() {
//		assert false : "what's the right string here?";
//		return mPvoc.toString();
		return mTerm.toString();
	}

	@Override
	public int getArity() {
		return mArity;
	}
	
	@Override
	public String toString() {
		return mTerm.toString();
	}

	@Override
	public boolean dependsOn(EqFunction f) {
		return this.equals(f);
	}

	@Override
	public boolean isStore() {
		return false;
	}
	
	@Override
	public EqFunction getFunction() {
		throw new AssertionError("check isStore() first");
	}
	
	@Override
	public List<EqNode> getStoreIndices() {
		throw new AssertionError("check isStore() first");
	}

	@Override
	public EqNode getValue() {
		throw new AssertionError("check isStore() first");
	}

	@Override
	public EqFunction getInnerMostFunction() {
		return this;
	}

}
