/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
import java.util.Map.Entry;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Class to represent a state in a non-relational domain
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class NonrelationalState<VALUE extends INonrelationalValue<VALUE>>
		implements IAbstractState<NonrelationalState<VALUE>> {
	private final Map<Term, VALUE> mVariablesToValues;

	/**
	 * Creates a new state with the given variable mapping.
	 */
	public NonrelationalState(final Map<Term, VALUE> variablesToValues) {
		mVariablesToValues = variablesToValues;
	}

	/**
	 * Creates a top state
	 */
	public NonrelationalState() {
		this(Map.of());
	}

	@Override
	public Term toTerm(final Script script) {
		final List<Term> conjunction = mVariablesToValues.entrySet().stream()
				.map(x -> x.getValue().toTerm(x.getKey(), script)).collect(Collectors.toList());
		return SmtUtils.and(script, conjunction);
	}

	private NonrelationalState<VALUE> merge(final NonrelationalState<VALUE> other,
			final BinaryOperator<VALUE> operator) {
		final Map<Term, VALUE> join = new HashMap<>();
		for (final Entry<Term, VALUE> entry : mVariablesToValues.entrySet()) {
			final Term var = entry.getKey();
			final VALUE otherValue = other.mVariablesToValues.get(var);
			if (otherValue == null) {
				// The variable is not present in the second state (i.e. it is top).
				// Therefore it is also top in the union and we omit it.
				continue;
			}
			final VALUE joinedValue = operator.apply(entry.getValue(), otherValue);
			if (!joinedValue.isTop()) {
				join.put(var, joinedValue);
			}
		}
		return new NonrelationalState<>(join);
	}

	@Override
	public NonrelationalState<VALUE> join(final NonrelationalState<VALUE> other) {
		return merge(other, VALUE::join);
	}

	@Override
	public NonrelationalState<VALUE> widen(final NonrelationalState<VALUE> other) {
		return merge(other, VALUE::widen);
	}

	@Override
	public boolean isBottom() {
		return mVariablesToValues.values().stream().anyMatch(VALUE::isBottom);
	}

	@Override
	public String toString() {
		return mVariablesToValues.toString();
	}
}
