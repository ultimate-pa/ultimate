package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class EqFunction implements IEqFunctionIdentifier<EqFunction> {
	
	
	
	private final IProgramVarOrConst mPvoc;
	private final Term mTerm;
	private final boolean mIsVersioned;
	private final EqNodeAndFunctionFactory mFactory;

	public EqFunction(IProgramVarOrConst pvoc, EqNodeAndFunctionFactory factory) {
		mPvoc = pvoc;
		mTerm = pvoc.getTerm();
		mIsVersioned = false;
		mFactory = factory;
	}
	
	public EqFunction(IProgramVarOrConst pvoc, Term term, EqNodeAndFunctionFactory factory) {
		mPvoc = pvoc;
		mTerm = term;
		mIsVersioned = true;
		mFactory = factory;
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

		assert false : "how to determine the procedure of a non-global constant??";
		return null;
	}

	public Term getTerm() {
		return mTerm;
	}

	@Override
	public EqFunction renameVariables(Map<Term, Term> substitutionMapping) {
		final Term renamed = substitutionMapping.get(mTerm);
		if (renamed == null) {
			return this;
		}
		return mFactory.getOrConstructEqFunction(mPvoc, renamed);
	}

	public IProgramVarOrConst getPvoc() {
		return mPvoc;
	}

	public String getFunctionName() {
		assert false : "what's the right string here?";
		return mPvoc.toString();
	}

	@Override
	public int getArity() {
		assert false : "TODO";
		return 0;
	}

}
