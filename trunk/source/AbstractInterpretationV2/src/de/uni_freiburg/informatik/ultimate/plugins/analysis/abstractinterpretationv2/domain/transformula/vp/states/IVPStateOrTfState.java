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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;

public abstract class IVPStateOrTfState<NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {
	
	protected final Set<IProgramVar> mVars;
	private Set<VPDomainSymmetricPair<NODEID>> mDisEqualitySet;
	private final boolean mIsTop;
	
	public IVPStateOrTfState(
			Set<VPDomainSymmetricPair<NODEID>> disEqs, 
			boolean isTop, 
			Set<IProgramVar> vars) {
		mDisEqualitySet = Collections.unmodifiableSet(disEqs);
		mIsTop = isTop;
		mVars = Collections.unmodifiableSet(vars);
	}
	
	public Set<NODEID> getDisequalities(NODEID nodeIdentifer) {
//		assert nodeIdentifer.getEqNode() != null;
		Set<NODEID> result = new HashSet<>();
		for (VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (pair.contains(nodeIdentifer)) {
				result.add(pair.getOther(nodeIdentifer));
			}
		}
		return result;
	}
	


	public Set<VPDomainSymmetricPair<NODEID>> getDisEqualities() {
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);
		return mDisEqualitySet;
	}

	abstract public boolean isBottom();

	public boolean isTop() {
		return mIsTop;
	}
	
	public Set<IProgramVar> getVariables() {
		return mVars;
	}

	/**
	 * just a convenient interface for the disequality set 
	 *  --> difference to areUnEqual: does not do a find(..) on the given nodes
	 * 
	 * @param nodeId1
	 * @param nodeId2
	 * @return
	 */
	public boolean containsDisEquality(NODEID nodeId1, NODEID nodeId2) {
		return mDisEqualitySet.contains(new VPDomainSymmetricPair<NODEID>(nodeId1, nodeId2));
	}	

	/**
	 * Determines if the given nodes are unequal in this state.
	 * (difference to containsDisEquality: does a find(..) on the nodes)
	 * @param nodeIdentifier1
	 * @param nodeIdentifier2
	 * @return
	 */
	public boolean areUnEqual(NODEID nodeIdentifier1, NODEID nodeIdentifier2) {
		NODEID find1 = find(nodeIdentifier1);
		NODEID find2 = find(nodeIdentifier2);
		return containsDisEquality(find1, find2);
	}
	
	public boolean areEqual(NODEID nodeIdentifier1, NODEID nodeIdentifier2) {
		NODEID find1 = find(nodeIdentifier1);
		NODEID find2 = find(nodeIdentifier2);
		return find1.equals(find2);
	}

	abstract public EqGraphNode<NODEID, ARRAYID> getEqGraphNode(NODEID nodeIdentifier);
	
	abstract public Set<EqGraphNode<NODEID, ARRAYID>> getAllEqGraphNodes();
	
	abstract public NODEID find(NODEID id);
	
	protected boolean isTopConsistent() {
		if (!mIsTop) {
			return true;
		}
		for (VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (!pair.getFirst().isLiteral() || !pair.getSecond().isLiteral()) {
				return false;
			}
		}
		
		for (EqGraphNode<NODEID, ARRAYID> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				return false;
			}
		}
		return true;
	}
}
