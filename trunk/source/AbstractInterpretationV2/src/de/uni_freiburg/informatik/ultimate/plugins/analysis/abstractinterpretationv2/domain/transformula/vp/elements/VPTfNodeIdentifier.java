/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Identifies an EqGraphNode in a VPTfState.
 *  - typically corresponds to a subterm of the VPTfState's TransFormula's Term
 *   exception: when the TransFormula talks about an array, then we introduce EqGraphNodes
 *     for all indices of that array which we track. Convention (for now?): these nodes
 *       may have null-values in their invar/outvar maps.
 * 
 * @author Alexander Nutz
 */
public class VPTfNodeIdentifier implements IEqNodeIdentifier<VPTfArrayIdentifier>, IElementWrapper {
	
	private final EqNode mEqNode;
//	private final Term mTerm;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final boolean mIsFunction;
	private final boolean mIsLiteral;
	private final VPTfArrayIdentifier mFunction;
	private final boolean mIsInOrThrough;

	private final NodeIdWithSideCondition mNodeIdWithSideCondition;


	public VPTfNodeIdentifier(EqNode eqNode, 
			Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars,
			VPTfStateBuilder tfStateBuilder) {
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
//			mFunction = getArrayIdentifier((EqFunctionNode) eqNode, inVars, outVars);
			mFunction = tfStateBuilder.getArrayIdentifier(
					((EqFunctionNode) eqNode).getFunction(), inVars, outVars);
		} else {
			mFunction = null;
		}
		
		mNodeIdWithSideCondition = new NodeIdWithSideCondition(this, Collections.emptySet(), Collections.emptySet());
		
//		/*
//		 * a nodeIdentifier has to be "pure" in the sense that it is either
//		 *  - "in" (i.e. there are variables that are inVars but no outVars)
//		 *  - "out" (i.e. there are variables that are outVars but no inVars)
//		 *  - "through" (i.e. all variables are both inVars and outVars)
//		 *  Than means it cannot have two variables where one is only in and one is only out. 
//		 *  
//		 *  TODO: the following computation is related to what VPDomainHelpers.computeInOutStatus(pv, tf) does
//		 *     --> perhaps merge
//		 */
//
//		boolean isIn = false;
//		boolean isOut = false;
//		for (Entry<IProgramVar, TermVariable> en : mInVars.entrySet()) {
//			if (!mOutVars.containsKey(en.getKey())) {
//				// we have an invar that is no outVar --> this node is "in"
//				isIn = true;
//			}
//		}
//		for (Entry<IProgramVar, TermVariable> en : mOutVars.entrySet()) {
//			if (!mInVars.containsKey(en.getKey())) {
//				// we have an outVar that is no inVar --> this node is "out"
//				// if it is already "in", then the sanity check fails
//				isOut = true;
//				assert !isIn;
//			}
//		}	
		
		/*
		 * new plan: 
		 * a node's inOutStatus is determined by its topmost symbol.
		 *  (in a[b[i]] that would be a for example)
		 */
		boolean isIn = false;
		boolean isOut = false;
		if (eqNode.mIsConstant) {
			isIn = true;
			isOut = true;
		} else {
			if (eqNode.isFunction()) {
				final IProgramVarOrConst function = eqNode.getFunction();
				assert function instanceof IProgramVar : "node should be constant"; 
				
				isIn = mInVars.containsKey(function);
				isOut = mOutVars.containsKey(function);
			} else {
				/*
				 * in case of a base node, we can just go over the variables
				 */
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
						isOut = true;
						assert !isIn;
					}
				}	
			}
		}
		
		mIsInOrThrough = isIn || (!isIn && !isOut);
		
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
		

		return true;
	}


//	private VPArrayIdentifier getArrayIdentifier(EqFunctionNode eqNode, 
//			Map<IProgramVar, TermVariable> inVars,
//			Map<IProgramVar, TermVariable> outVars) {
//		IProgramVarOrConst pvoc = eqNode.getFunction();
//		// TODO: --> perhaps write a management for array identifiers, so they are unique..
//		return new VPArrayIdentifier(pvoc, inVars, outVars);
////		if (pvoc.getTerm() instanceof ConstantTerm || 
////				((pvoc.getTerm() instanceof ApplicationTerm) 
////						&& ((ApplicationTerm) pvoc.getTerm()).getParameters().length == 0)) {
////			return new VPArrayIdentifier(pvoc.getTerm());
////		}
////		if (inVars.containsKey(pvoc)) {
////			return new VPArrayIdentifier(inVars.get(pvoc));
////		}
////		if (outVars.containsKey(pvoc)) {
////			return new VPArrayIdentifier(outVars.get(pvoc));
////		}
////		assert false;
////		return null;
//	}


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
	
	public VPTfArrayIdentifier getFunction() {
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
			return "NodeId(#" + Integer.toString(this.hashCode()).substring(0, 3) + "): " + mEqNode;
//		} else if (mIdentifyingTerm != null) {
//			return "NodeId: " + mTerm;
//		} else {
//			assert false;
//			return null;
//		}
	}
	
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPTfNodeIdentifier)) {
			return false;
		}
		if (this == other) {
			return true;
		}
		
		VPTfNodeIdentifier otherNodeId = (VPTfNodeIdentifier) other;

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


	public boolean isInOrThrough() {
		return mIsInOrThrough;
	}





	@Override
	public Set<NodeIdWithSideCondition> getNodeIdWithSideConditions(VPTfState tfState) {
		return Collections.singleton(mNodeIdWithSideCondition);
	}

//	@Override
//	public Set<ISingleElementWrapper> getElements() {
//		return Collections.singleton(this);
//	}
}
