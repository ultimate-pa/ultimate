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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.CreateVanillaTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;
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
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final boolean mIsFunction;
	private final boolean mIsLiteral;
	private final VPTfArrayIdentifier mFunction;
	private final Set<VPTfArrayIdentifier> mAllFunctions;
	protected final TfNodeInOutStatus mInOutStatus;

	private final NodeIdWithSideCondition mNodeIdWithSideCondition;

	/**
	 * super constructor exclusively for VpTfExtraNodeIdentifier
	 * @param eqNode
	 * @param inOutStatus 
	 */
	protected VPTfNodeIdentifier(final EqNode eqNode, final TfNodeInOutStatus inOutStatus) {
		this.mEqNode = eqNode;

		assert !(eqNode instanceof EqFunctionNode);
		this.mIsFunction = false;
		this.mFunction = null;

		this.mIsLiteral = eqNode.isLiteral();
		
		mNodeIdWithSideCondition = new NodeIdWithSideCondition(this, Collections.emptySet(), Collections.emptySet());
		
		mInOutStatus = inOutStatus;

		Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		if (inOutStatus == TfNodeInOutStatus.IN || inOutStatus == TfNodeInOutStatus.THROUGH) {
			for (IProgramVar var : eqNode.getVariables()) {
				inVars.put(var, null);
			}
		}
		mInVars = inVars;

		Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		if (inOutStatus == TfNodeInOutStatus.OUT || inOutStatus == TfNodeInOutStatus.THROUGH) {
			for (IProgramVar var : eqNode.getVariables()) {
				outVars.put(var, null);
			}
		}
		mOutVars = outVars;
		
		
		mAllFunctions = Collections.emptySet();

	}

	public VPTfNodeIdentifier(EqNode eqNode, 
			Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars,
//			VPTfStateBuilder tfStateBuilder) {
			CreateVanillaTfStateBuilder tfStateBuilder) {
		this.mEqNode = eqNode;
		this.mIsFunction = eqNode instanceof EqFunctionNode;

		this.mIsLiteral = eqNode.isLiteral();
		if (mIsFunction) {
			mFunction = tfStateBuilder.getOrConstructArrayIdentifier(
					((EqFunctionNode) eqNode).getFunction(), inVars, outVars);
		} else {
			mFunction = null;
		}
		// compute all function symbols in this node and its descendants (used only for debugging, if at all)
		if (mIsFunction) {
			Set<VPTfArrayIdentifier> allFunctions = new HashSet<>();
			for (EqNode argEqn : ((EqFunctionNode) eqNode).getArgs()) {
				if (argEqn instanceof EqFunctionNode) {
					allFunctions.add(tfStateBuilder.getOrConstructArrayIdentifier(
							((EqFunctionNode) argEqn).getFunction(), inVars, outVars));
				}
			
			}
			allFunctions.add(mFunction);
			mAllFunctions = Collections.unmodifiableSet(allFunctions);
		} else {
			mAllFunctions = Collections.emptySet();
		}
		
		this.mInVars = Collections.unmodifiableMap(inVars);
		this.mOutVars = Collections.unmodifiableMap(outVars);
		
		mNodeIdWithSideCondition = new NodeIdWithSideCondition(this, Collections.emptySet(), Collections.emptySet());
		
		/*
		 * new plan (2.0):
		 *  introduced enum TfNodeInOutStatus
		 */
		if (eqNode.mIsConstant) {
			mInOutStatus = TfNodeInOutStatus.THROUGH;
		} else {
			/**
			 * is there a var that is only in inVars?
			 */
			boolean hasExclusiveIn = false;
			/**
			 * is there a var that is only in outVars?
			 */
			boolean hasExclusiveOut = false;
			/**
			 * is there a var that is both in inVars and in outVars?
			 * (assuming that this implies that it has the same TermVariable in both cases, see assertions below)
			 */
			boolean hasThrough = false;


			for (Entry<IProgramVar, TermVariable> en : mInVars.entrySet()) {
				if (!mOutVars.containsKey(en.getKey())) {

				}
				// we have an invar 
				if (mOutVars.containsKey(en.getKey())) {
					// en.getKey is both in and out
					assert en.getValue() == mOutVars.get(en.getKey()) : 
						"we have an EqGraphNode with both update-versions of a variable -- can this really happen?";
					hasThrough = true;
				} else {
					hasExclusiveIn = true;
				}
			}
			for (Entry<IProgramVar, TermVariable> en : mOutVars.entrySet()) {
				if (mInVars.containsKey(en.getKey())) {
					// en.getKey is both in and out
					assert en.getValue() == mInVars.get(en.getKey()) : 
						"we have an EqGraphNode with both update-versions of a variable -- can this really happen?";
					hasThrough = true;
				} else {
					hasExclusiveOut = true;
				}
			}	
			
			if (hasExclusiveIn && hasExclusiveOut) {
				mInOutStatus = TfNodeInOutStatus.MIXED;
			} else if (hasExclusiveIn && !hasExclusiveOut) {
				mInOutStatus = TfNodeInOutStatus.IN;
			} else if (!hasExclusiveIn && hasExclusiveOut) {
				mInOutStatus = TfNodeInOutStatus.OUT;
			} else {
				if (hasThrough) {
					mInOutStatus = TfNodeInOutStatus.THROUGH;
				} else {
					assert false : "node is constant, right?..";
					mInOutStatus = TfNodeInOutStatus.THROUGH;
				}
			}
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

		return true;
	}

	public EqNode getEqNode() {
		return mEqNode;
	}

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
		return "NodeId(" + mInOutStatus + "): " + mEqNode;
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

	public boolean isOutOrThrough() {
		return mInOutStatus == TfNodeInOutStatus.OUT || mInOutStatus == TfNodeInOutStatus.THROUGH;
	}

	public boolean isInOrThrough() {
		return mInOutStatus == TfNodeInOutStatus.IN || mInOutStatus == TfNodeInOutStatus.THROUGH;
	}

	@Override
	public Set<NodeIdWithSideCondition> getNodeIdWithSideConditions(VPTfState tfState) {
		return Collections.singleton(mNodeIdWithSideCondition);
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	@Override
	public Collection<VPTfArrayIdentifier> getAllFunctions() {
		return mAllFunctions;
	}
}

