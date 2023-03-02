/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2019-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class IntervalState implements IAbstractState<IntervalState> {
	private final Map<Term, Interval> mVariablesToValues;

	public IntervalState(final Map<Term, Interval> variablesToValues) {
		mVariablesToValues = variablesToValues;
	}

	public IntervalState() {
		this(Map.of());
	}

	@Override
	public Term toTerm(final Script script) {
		final List<Term> conjunction = mVariablesToValues.entrySet().stream()
				.map(x -> x.getValue().toTerm(x.getKey(), script)).collect(Collectors.toList());
		return SmtUtils.and(script, conjunction);
	}

	private IntervalState merge(final IntervalState other, final BinaryOperator<Interval> operator) {
		final Set<Term> allVars =
				DataStructureUtils.union(mVariablesToValues.keySet(), other.mVariablesToValues.keySet());
		final Map<Term, Interval> join = new HashMap<>();
		for (final Term var : allVars) {
			final Interval value1 = mVariablesToValues.getOrDefault(var, Interval.TOP);
			final Interval value2 = other.mVariablesToValues.getOrDefault(var, Interval.TOP);
			final Interval joinedValue = operator.apply(value1, value2);
			if (!joinedValue.isTop()) {
				join.put(var, joinedValue);
			}
		}
		return new IntervalState(join);
	}

	@Override
	public IntervalState join(final IntervalState other) {
		return merge(other, Interval::union);
	}

	@Override
	public IntervalState widen(final IntervalState other) {
		return merge(other, Interval::widen);
	}
}
