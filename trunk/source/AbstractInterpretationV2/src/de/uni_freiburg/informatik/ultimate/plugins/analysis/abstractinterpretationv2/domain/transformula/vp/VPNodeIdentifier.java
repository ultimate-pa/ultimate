package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class VPNodeIdentifier {
	
	private final EqNode mEqNode;
	private final Term mIdentifyingTerm;
	private final boolean mIsFunction;
	private final boolean mIsLiteral;
	private final VPArrayIdentifier mFunction;

	public VPNodeIdentifier(EqNode eqNode) {
		this.mEqNode = eqNode;
		this.mIsFunction = eqNode instanceof EqFunctionNode;
		this.mIdentifyingTerm = null;
		this.mIsLiteral = eqNode.isLiteral();
		if (mIsFunction) {
			mFunction = new VPArrayIdentifier(((EqFunctionNode) eqNode).getFunction());
		} else {
			mFunction = null;
		}
	}

	public VPNodeIdentifier(Term term) {
		this.mEqNode = null;
		this.mIsFunction = term instanceof ApplicationTerm 
				&& (((ApplicationTerm) term).getFunction().getName().equals("select")
						|| ((ApplicationTerm) term).getFunction().getName().equals("store"));

		this.mIdentifyingTerm = term;
		this.mIsLiteral = term instanceof ConstantTerm;
		if (mIsFunction) {
			ApplicationTerm at = (ApplicationTerm) term;
			mFunction = new VPArrayIdentifier(getArrayTerm(at));
		} else {
			mFunction = null;
		}
	}

	public EqNode getEqNode() {
		return mEqNode;
	}

	public Term getTerm(ManagedScript script) {
		if (mIdentifyingTerm != null) {
			return mIdentifyingTerm;
		}
		return mEqNode.getTerm(script);
	}

	public Term getIdTerm() {
		return mIdentifyingTerm;
	}

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
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPNodeIdentifier)) {
			return false;
		}
		VPNodeIdentifier otherNodeId = (VPNodeIdentifier) other;
		
		if (this.mEqNode != otherNodeId.mEqNode) {
			return false;
		}
		
		if (this.mIdentifyingTerm != otherNodeId.mIdentifyingTerm) {
			if (this.isFunction()) {
				// one term might be a store, one a select
				Term thisArray = getArrayTerm((ApplicationTerm) this.mIdentifyingTerm);
				Term otherArray = getArrayTerm((ApplicationTerm) otherNodeId.mIdentifyingTerm);
				
				if (thisArray != otherArray) {
					return false;
				}
				
				ArrayIndex thisIndices = getArrayIndices((ApplicationTerm) this.mIdentifyingTerm);
				ArrayIndex otherIndices = getArrayIndices((ApplicationTerm) otherNodeId.mIdentifyingTerm);
				assert thisIndices.size() == otherIndices.size();
				for (int i = 0; i < thisIndices.size(); i++) {
					if (!new VPNodeIdentifier(thisIndices.get(i))
							.equals(new VPNodeIdentifier(otherIndices.get(i)))) {
						return false;
					}
				}
			} else {
				return false;
			}
		}
		
		return true;
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

	private Term getArrayTerm(ApplicationTerm at) {
		if (at.getFunction().getName().equals("select")) {
			MultiDimensionalSelect mds = new MultiDimensionalSelect(at);
			return mds.getArray();
		} else if (at.getFunction().getName().equals("store")) {
			MultiDimensionalStore mds = new MultiDimensionalStore(at);
			return mds.getArray();
		} else {
			assert false;
			return null;
		}
	}
	
	@Override
	public String toString() {
		if (mEqNode != null) {
			return "NodeId: " + mEqNode;
		} else if (mIdentifyingTerm != null) {
			return "NodeId: " + mIdentifyingTerm;
		} else {
			assert false;
			return null;
		}
	}

	@Override
	public int hashCode() {
		// TODO
		return 0;
	}
}
