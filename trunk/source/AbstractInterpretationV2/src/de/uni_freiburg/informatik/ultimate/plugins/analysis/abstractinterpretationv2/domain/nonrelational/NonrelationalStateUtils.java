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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

/**
 * Utilitiy functions for nonrelational domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class NonrelationalStateUtils {

	/**
	 * Merges states in a given list of {@link NonrelationalEvaluationResult}s if the number of elements in the list is
	 * more than the given number of allowed elements.
	 *
	 * @param results
	 *            The list of {@link NonrelationalEvaluationResult}s.
	 * @param maxParallelStates
	 *            The number of total allowed states to keep in the list.
	 * @return A list that contains the reulst of merging all results.
	 */
	public static <VALUE extends INonrelationalValue<VALUE>> List<IEvaluationResult<VALUE>>
			mergeIfNecessary(final List<IEvaluationResult<VALUE>> results, final int maxParallelStates) {

		if (results.size() > maxParallelStates) {
			return Collections.singletonList(results.stream().reduce(NonrelationalStateUtils::merge).get());
		}

		return results;
	}

	private static <VALUE extends INonrelationalValue<VALUE>> IEvaluationResult<VALUE>
			merge(final IEvaluationResult<VALUE> a, final IEvaluationResult<VALUE> b) {
		return new NonrelationalEvaluationResult<>(a.getValue().merge(b.getValue()),
				a.getBooleanValue().merge(b.getBooleanValue()));
	}
}
