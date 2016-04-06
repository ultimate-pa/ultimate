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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

/**
 * Utilitiy functions for the Congruence domain.
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CongruenceUtils {

	/**
	 * Merges states in a given list of {@link CongruenceDomainValue}s if the elements in the list are more than the
	 * specified number of elements.
	 * 
	 * @param results
	 *            The list of {@link CongruenceDomainValue}s.
	 * @param maxParallelStates
	 *            The largest allowed number of singular {@link CongruenceDomainValue}s in the list.
	 * @return A new list that contains the result of merging all {@link CongruenceDomainValue}s in the given list.
	 */
	protected static List<IEvaluationResult<CongruenceDomainValue>> mergeIfNecessary(
	        final List<IEvaluationResult<CongruenceDomainValue>> results, final int maxParallelStates) {
		if (results.size() > maxParallelStates) {
			return Collections.singletonList(results.stream().reduce(CongruenceUtils::merge).get());
		}
		return results;
	}

	/**
	 * Merges states in a given list of {@link CongruenceDomainState}s if the elements in the list are more than the
	 * specified number of elements.
	 * 
	 * @param results
	 *            The list of {@link CongruenceDomainState}s.
	 * @param maxParallelStates
	 *            The largest allowed number of singular {@link CongruenceDomainState}s in the given list.
	 * @return A new list that contains the result of merging all {@link CongruenceDomainState}s in the given list.
	 */
	protected static List<CongruenceDomainState> mergeStatesIfNecessary(final List<CongruenceDomainState> results,
	        final int maxParallelStates) {
		if (results.size() > maxParallelStates) {
			return Collections.singletonList(results.stream().reduce(CongruenceUtils::merge).get());
		}
		return results;
	}

	private static IEvaluationResult<CongruenceDomainValue> merge(final IEvaluationResult<CongruenceDomainValue> res1,
	        final IEvaluationResult<CongruenceDomainValue> res2) {
		return new CongruenceDomainEvaluationResult(res1.getValue().merge(res2.getValue()),
		        res1.getBooleanValue().merge(res2.getBooleanValue()));
	}

	private static CongruenceDomainState merge(final CongruenceDomainState state1, final CongruenceDomainState state2) {
		return state1.merge(state2);
	}
}
