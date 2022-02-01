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

import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;

/**
 * Utilitiy functions for non-relational domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class NonrelationalUtils {

	private NonrelationalUtils() {
		// do not instantiate util class
	}

	/**
	 * Merges states in a given list of {@link INonrelationalValue}s if the elements in the list are more than the
	 * specified number of elements.
	 *
	 * @param results
	 *            The list of {@link INonrelationalValue}s.
	 * @param maxParallelStates
	 *            The largest allowed number of singular {@link IntervalDomainValue}s in the list.
	 * @return A new list that contains the result of merging all {@link IntervalDomainValue}s in the given list.
	 */
	public static <V extends INonrelationalValue<V>> Collection<IEvaluationResult<V>>
			mergeIfNecessary(final Collection<IEvaluationResult<V>> results, final int maxParallelStates) {
		if (results.size() <= maxParallelStates) {
			return results;
		}
		return Collections.singletonList(results.stream().reduce(NonrelationalUtils::merge).get());
	}

	/**
	 * Merges states in a given list of {@link IntervalDomainState}s if the elements in the list are more than the
	 * specified number of elements.
	 *
	 * @param results
	 *            The list of {@link IntervalDomainState}s.
	 * @param maxParallelStates
	 *            The largest allowed number of singular {@link IntervalDomainState}s in the given list.
	 * @return A new list that contains the result of merging all {@link IntervalDomainState}s in the given list.
	 */
	public static <STATE extends IAbstractState<STATE>> Collection<STATE>
			mergeStatesIfNecessary(final Collection<STATE> results, final int maxParallelStates) {
		if (results.size() > maxParallelStates) {
			return Collections.singletonList(results.stream().reduce(NonrelationalUtils::merge).get());
		}
		return results;
	}

	private static <V extends INonrelationalValue<V>> IEvaluationResult<V> merge(final IEvaluationResult<V> a,
			final IEvaluationResult<V> b) {
		return new NonrelationalEvaluationResult<>(a.getValue().merge(b.getValue()),
				a.getBooleanValue().merge(b.getBooleanValue()));
	}

	private static <STATE extends IAbstractState<STATE>> STATE merge(final STATE a, final STATE b) {
		return a.union(b);
	}
}
