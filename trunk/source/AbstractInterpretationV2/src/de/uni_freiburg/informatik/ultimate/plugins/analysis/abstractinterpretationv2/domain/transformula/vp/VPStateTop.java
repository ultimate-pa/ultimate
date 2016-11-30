/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
*
* @author Yu-Wen Chen (yuwenchen1105@gmail.com)
*
*/
public class VPStateTop extends VPState {
	
	VPStateTop(Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			Set<VPDomainSymmetricPair<EqGraphNode>> disEqualitySet, VPDomain domain) {
		super(eqNodeToEqGraphNodeMap, disEqualitySet, domain);
		this.clearState();
	}
	
	@Override
	public boolean isBottom() {
		return false;
	}

	@Override
	public VPState addVariable(IProgramVar variable) {
		// Do nothing
		return this;
	}

	@Override
	public VPState removeVariable(IProgramVar variable) {
		// Do nothing
		return this;
	}

	@Override
	public VPState addVariables(Collection<IProgramVar> variables) {
		// Do nothing
		return this;
	}

	@Override
	public VPState removeVariables(Collection<IProgramVar> variables) {
		// Do nothing
		return this;
	}

	@Override
	public VPState copy() {
		return super.copy();
	}

	@Override
	public boolean containsVariable(IProgramVar var) {
		// Do nothing
		return false;
	}

	@Override
	public Set<IProgramVar> getVariables() {
		// Do nothing
		return null;
	}

	@Override
	public VPState patch(VPState dominator) {
		// Auto-generated method stub
		return super.patch(dominator);
	}

	@Override
	public boolean isEmpty() {
		// Auto-generated method stub
		return super.isEmpty();
	}

	@Override
	public boolean isEqualTo(VPState other) {
		// Auto-generated method stub
		return super.isEqualTo(other);
	}

	@Override
	public SubsetResult isSubsetOf(
			VPState other) {
		// Auto-generated method stub
		return super.isSubsetOf(other);
	}

	@Override
	public String toLogString() {
		
		return "Top state.";
	}

	@Override
	public boolean equals(Object obj) {
		// Auto-generated method stub
		return super.equals(obj);
	}
	
}
