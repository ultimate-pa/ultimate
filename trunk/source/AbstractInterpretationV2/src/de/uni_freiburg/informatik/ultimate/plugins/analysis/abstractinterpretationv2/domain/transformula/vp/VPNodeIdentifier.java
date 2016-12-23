package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class VPNodeIdentifier implements IEqNodeIdentifier<VPArrayIdentifier> {
	
	private final EqNode mEqNode;
//	private final Term mTerm;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final boolean mIsFunction;
	private final boolean mIsLiteral;
	private final VPArrayIdentifier mFunction;


	public VPNodeIdentifier(EqNode eqNode, 
			Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		this.mEqNode = eqNode;
//		this.mIsFunction = term instanceof ApplicationTerm 
//				&& (((ApplicationTerm) term).getFunction().getName().equals("select")
//						|| ((ApplicationTerm) term).getFunction().getName().equals("store"));
		this.mIsFunction = eqNode instanceof EqFunctionNode;

//		this.mTerm = term;
		this.mInVars = Collections.unmodifiableMap(inVars);
		this.mOutVars = Collections.unmodifiableMap(outVars);
		this.mIsLiteral = eqNode.isLiteral();
		if (mIsFunction) {
//			ApplicationTerm at = (ApplicationTerm) term;
//			mFunction = new VPArrayIdentifier(getArrayTerm(at));
			mFunction = getArrayIdentifier((EqFunctionNode) eqNode, inVars, outVars);
		} else {
			mFunction = null;
		}
		
		assert sanityCheck();
	}


	private boolean sanityCheck() {
		/*
		 * If an IProgramVar appears both in inVars and outVars, both maps have to assign it the same TermVariable
		 * (intuition: a VPNodeIdentifier corresponds to _one_ Term over constants and TermVariables)
		 */
		for (Entry<IProgramVar, TermVariable> en : mInVars.entrySet()) {
			if (mOutVars.containsKey(en.getKey())
					&& mOutVars.get(en.getKey()) != en.getValue()) {
				return false;
			}
		}
		
		/*
		 * a nodeIdentifier has to be "pure" in the sense that it is either
		 *  - "in" (i.e. there are variables that are inVars but no outVars)
		 *  - "out" (i.e. there are variables that are outVars but no inVars)
		 *  - "through" (i.e. all variables are both inVars and outVars)
		 *  Than means it cannot have two variables where one is only in and one is only out. 
		 */
		boolean isIn = false;
		for (Entry<IProgramVar, TermVariable> en : mInVars.entrySet()) {
			if (!mOutVars.containsKey(en.getKey())) {
				// we have an invar that is no outVar --> this node is "in"
				isIn = true;
			}
		}
		for (Entry<IProgramVar, TermVariable> en : mOutVars.entrySet()) {
			if (!mInVars.containsKey(en.getKey())) {
				// we have an outVar that is no inVar --> this node is "out"
				// if it is already "in", then the sanity check fails
				if (isIn) {
					return false;
				}
			}
		}	
		return true;
	}


	private VPArrayIdentifier getArrayIdentifier(EqFunctionNode eqNode, 
			Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		IProgramVarOrConst pvoc = eqNode.getFunction();
		if (pvoc.getTerm() instanceof ConstantTerm || 
				((pvoc.getTerm() instanceof ApplicationTerm) 
						&& ((ApplicationTerm) pvoc.getTerm()).getParameters().length == 0)) {
			return new VPArrayIdentifier(pvoc.getTerm());
		}
		if (inVars.containsKey(pvoc)) {
			return new VPArrayIdentifier(inVars.get(pvoc));
		}
		if (outVars.containsKey(pvoc)) {
			return new VPArrayIdentifier(outVars.get(pvoc));
		}
		assert false;
		return null;
	}


	public EqNode getEqNode() {
		return mEqNode;
	}

//	public Term getTerm(ManagedScript script) {
//		return mTerm;
////		if (mIdentifyingTerm != null) {
////			return mIdentifyingTerm;
////		}
////		return mEqNode.getTerm(script);
//	}

//	public Term getIdTerm() {
//		return mIdentifyingTerm;
//	}

	public boolean isFunction() {
		return mIsFunction;
	}
	
	public VPArrayIdentifier getFunction() {
		assert mIsFunction : "check isFunction() before";
		return mFunction;
	}
	
	public boolean isLiteral() {
		return mIsLiteral;
	}
	
	
		
	private ArrayIndex getArrayIndices(ApplicationTerm at) {
		if (at.getFunction().getName().equals("select")) {
			MultiDimensionalSelect mds = new MultiDimensionalSelect(at);
			return mds.getIndex();
		} else if (at.getFunction().getName().equals("store")) {
			MultiDimensionalStore mds = new MultiDimensionalStore(at);
			return mds.getIndex();
		} else {
			assert false;
			return null;
		}
	}


	
	@Override
	public String toString() {
//		if (mEqNode != null) {
			return "NodeId: " + mEqNode;
//		} else if (mIdentifyingTerm != null) {
//			return "NodeId: " + mTerm;
//		} else {
//			assert false;
//			return null;
//		}
	}
	
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPNodeIdentifier)) {
			return false;
		}
		if (this == other) {
			return true;
		}
		
		VPNodeIdentifier otherNodeId = (VPNodeIdentifier) other;

		if (this.mEqNode == otherNodeId.mEqNode 
				&& this.mInVars.equals(otherNodeId.mInVars)
				&& this.mOutVars.equals(otherNodeId.mOutVars)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashHsieh(31, mEqNode, mInVars, mOutVars);
	}
}
