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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The VPArrayIdentifier identifies an array occurence inside a TransFormula.
 * Analogously to the VPNodeIdentifier it consists of
 *  - what identifies an array in a VPState --> an IProgramVarOrConst (an EqNode in case of the VPNodeIdentifier)
 *  - inVar and outVar mappings --> here, pairs suffice, they may be null, if the array id is not in/ not out
 *  
 *  in principle it is possible to reconstruct a term from these, which occurs in the TransFormula we
 *  created this identifier for.
 *  
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class VPTfArrayIdentifier implements IArrayWrapper {
	
	private final IProgramVarOrConst mPvoc;
	private final Pair<IProgramVar, TermVariable> mInVar;
	private final Pair<IProgramVar, TermVariable> mOutVar;
//	private Term mTerm;
	private final ArrayInOutStatus mInOutStatus;
	
	protected VPTfArrayIdentifier(IProgramVarOrConst pvoc, ArrayInOutStatus inOutStatus) {
		assert pvoc != null : "investigate this case";
		mPvoc = pvoc;
//		mTerm = null; //TODO: makes sense?
		if (pvoc instanceof IProgramVar 
				&& (inOutStatus == ArrayInOutStatus.IN || inOutStatus == ArrayInOutStatus.THROUGH)) {
			mInVar = new Pair<>((IProgramVar) pvoc, null);
//			mTerm = pvoc.getTerm();
		} else {
			mInVar = null;
		}
		if (pvoc instanceof IProgramVar 
				&& (inOutStatus == ArrayInOutStatus.OUT || inOutStatus == ArrayInOutStatus.THROUGH)) {
			mOutVar = new Pair<>((IProgramVar) pvoc, null);
//			mTerm = mTerm == null ? pvoc.getTerm() : mTerm;
		} else {
			mOutVar = null;
		}
		mInOutStatus = inOutStatus;
	}

	public VPTfArrayIdentifier(IProgramVarOrConst pvoc, 
			Pair<IProgramVar, TermVariable> inVar, 
			Pair<IProgramVar, TermVariable> outVar) {
		assert pvoc != null : "investigate this case";
		mPvoc = pvoc;
		
//		if (inVar != null) {
//			mTerm = inVar.getSecond();
//		}
		mInVar = inVar;
		
		mOutVar = outVar;
//		if (outVar != null) {
//			mTerm = outVar.getSecond();
//		}
	
//		if (mTerm == null) {
//			assert pvoc instanceof ConstOrLiteral;
//			mTerm = pvoc.getTerm();
//		}
		
		if (inVar == null && outVar != null) {
			mInOutStatus = ArrayInOutStatus.OUT;
		} else if (inVar != null && outVar == null) {
			mInOutStatus = ArrayInOutStatus.IN;
		} else if (inVar != null && outVar != null) {
			mInOutStatus = ArrayInOutStatus.THROUGH;
		} else {
			mInOutStatus = ArrayInOutStatus.AUX;
			assert false : "do we deal with this case correctly?";
		}
	}
	
	public IProgramVarOrConst getProgramVarOrConst() {
		return mPvoc;
	}
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPTfArrayIdentifier)) {
			return false;
		}
		if (this == other) {
			return true;
		}
		VPTfArrayIdentifier otherArrayId = (VPTfArrayIdentifier) other;
		boolean result = //this.mTerm == otherArrayId.mTerm &&
				this.mPvoc == otherArrayId.mPvoc
				&& this.mInOutStatus == otherArrayId.mInOutStatus
				&& ((this.mInVar == null && otherArrayId.mInVar == null) || this.mInVar.equals(otherArrayId.mInVar))
				&& ((this.mOutVar == null && otherArrayId.mOutVar == null) || this.mOutVar.equals(otherArrayId.mOutVar));
		assert !result : "we manage ArrayIdentifiers such that they are unique, right??";
		return result;
	}
	
	@Override
	public String toString() {
		if (mPvoc != null) {
			return "ArrayId: " + mPvoc.toString();
		}
//		if (mTerm != null) {
//			return "ArrayId: " + mTerm.toString();
//		}
		assert false;
		return null;
	}

	@Override
	public int hashCode() {
//		return HashUtils.hashHsieh(31, mPvoc, mInVar, mOutVar, mTerm); // does not work as m[In|Out]Var can be null
//		return HashUtils.hashHsieh(31, mTerm);

//		return HashUtils.hashHsieh(31, mPvoc, mInVar, mOutVar, mTerm); // does not work as m[In|Out]Var can be null
//		return HashUtils.hashHsieh(31, hashObjects); // does not work as m[In|Out]Var can be null
		return HashUtils.hashHsieh(31, mPvoc, mInOutStatus);
//		return 
	}


	@Override
	public Set<ArrayWithSideCondition> getArrayWithSideConditions(VPTfState tfState, 
			Set<List<NodeIdWithSideCondition>> requestedIndices) {
		
		Set<VPTfNodeIdentifier> functionNodeIds = tfState.getFunctionNodesForArray(this);

		/*
		 * in case of a "plain" array (i.e. one not created through a store) the mapping form
		 * index to value is essentially the collection of function nodes for the array
		 *  e.g. say for array a we track the indices i and j
		 *    then the map will contain the pairs (i, a[i]) and (j, a[j])
		 */
		Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> indexToValue = new HashMap<>();
		for (VPTfNodeIdentifier fnid : functionNodeIds) {
			// obtain the indices via initCcchild
			List<VPTfNodeIdentifier> index = 
					tfState.getEqGraphNode(fnid).getInitCcchild().stream()
						.map(egn -> egn.mNodeIdentifier).collect(Collectors.toList());
			
			indexToValue.put(index, fnid);
		}

		ArrayWithSideCondition awsc = new ArrayWithSideCondition(indexToValue, 
				Collections.emptySet(), Collections.emptySet());
		return Collections.singleton(awsc);
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		if (mInVar == null) {
			return Collections.emptyMap();
		} else {
			assert mInVar.getSecond() != null;
			return Collections.singletonMap(mInVar.getFirst(), mInVar.getSecond());
		}
	}
	
	public Map<IProgramVar, TermVariable> getOutVars() {
		if (mOutVar == null) {
			return Collections.emptyMap();
		} else {
			assert mOutVar.getSecond() != null;
			return Collections.singletonMap(mOutVar.getFirst(), mOutVar.getSecond());
		}
	}

	@Override
	public VPTfArrayIdentifier getBaseArray() {
		return this;
	}
	
	public boolean isInOrThrough() {
		return mInOutStatus == ArrayInOutStatus.IN || mInOutStatus == ArrayInOutStatus.THROUGH;
	}

	public boolean isOutOrThrough() {
		return mInOutStatus == ArrayInOutStatus.OUT || mInOutStatus == ArrayInOutStatus.THROUGH;
	}

	public ArrayInOutStatus getInOutStatus() {
		return mInOutStatus;
	}
}

