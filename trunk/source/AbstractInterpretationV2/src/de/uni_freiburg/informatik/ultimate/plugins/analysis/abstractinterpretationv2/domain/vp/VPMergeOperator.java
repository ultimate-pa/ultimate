/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;

/**
 * The implementation of a simple merge operator on the VP domain. This operator
 * can also be used as widening operator.
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class VPMergeOperator implements
		IAbstractStateBinaryOperator<VPDomainState> {

	protected VPMergeOperator() {
	}

	/**
	 * Merges two abstract states, first and second, into one new abstract
	 * state. <br />
	 * 
	 * @param first
	 *            The first state to merge.
	 * @param second
	 *            The second state to merge.
	 */
	@Override
	public VPDomainState apply(VPDomainState first, VPDomainState second) {

		if (first == null) {
			return second;
		}
		
		if (second == null) {
			return first;
		}

		final VPDomainState newState = first.copy();

		final Map<String, Set<Expression>> mergeExprMap = new HashMap<String, Set<Expression>>(
				first.getExpressionMap());
		final Set<Expression> mergeExprSet = new HashSet<Expression>(
				first.getExprSet());
		final Map<String, Set<Expression>> mergePtrReadinMap = new HashMap<String, Set<Expression>>(
				first.getPtrReadintMap());

		for (final String key : second.getExpressionMap().keySet()) {
			if (!mergeExprMap.containsKey(key)) {
				mergeExprMap.put(key, second.getExpressionMap().get(key));
			} else {
				mergeExprMap.get(key).addAll(
						second.getExpressionMap().get(key));
			}
		}

		mergeExprSet.addAll(second.getExprSet());
		
		for (final String key : second.getPtrReadintMap().keySet()) {
			if (!mergePtrReadinMap.containsKey(key)) {
				mergePtrReadinMap.put(key, second.getPtrReadintMap().get(key));
			} else {
				mergePtrReadinMap.get(key).addAll(
						second.getPtrReadintMap().get(key));
			}
		}
		
		newState.setExpressionMap(mergeExprMap);
		newState.setExpressionSet(mergeExprSet);
		newState.setPtrReadinMap(mergePtrReadinMap);

		return newState;
	}


}
