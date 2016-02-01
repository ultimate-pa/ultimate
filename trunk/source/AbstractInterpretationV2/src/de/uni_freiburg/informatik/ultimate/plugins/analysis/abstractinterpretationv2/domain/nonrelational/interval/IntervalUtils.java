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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

/**
 * Utilitiy functions for the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalUtils {
	protected static List<IEvaluationResult<IntervalDomainEvaluationResult>> mergeIfNecessary(
	        final List<IEvaluationResult<IntervalDomainEvaluationResult>> results, int maxParallelStates) {
		if (results.size() > maxParallelStates) {
			return Collections.singletonList(results.stream().reduce(IntervalUtils::merge).get());
		}
		return results;
	}

	private static IEvaluationResult<IntervalDomainEvaluationResult> merge(
	        final IEvaluationResult<IntervalDomainEvaluationResult> a,
	        final IEvaluationResult<IntervalDomainEvaluationResult> b) {
		final IntervalDomainEvaluationResult left = a.getResult();
		final IntervalDomainEvaluationResult right = b.getResult();
		return new IntervalDomainEvaluationResult(left.getEvaluatedValue().merge(right.getEvaluatedValue()),
		        left.getEvaluatedState().merge(right.getEvaluatedState()),
		        left.getBooleanValue().merge(right.getBooleanValue()));
	}
}
