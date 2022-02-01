/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.counting.datastructures;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Represents a conjunction of atomic counter guards. As usual, an empty
 * conjunction represents 'true'.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ConjunctiveCounterFormula {

	private final LinkedHashSet<IAtomicCounterGuard> mConjuncts;

	public ConjunctiveCounterFormula(final LinkedHashSet<IAtomicCounterGuard> conjuncts) {
		super();
		Objects.nonNull(conjuncts);
		mConjuncts = conjuncts;
	}

	public Set<IAtomicCounterGuard> getConjuncts() {
		return Collections.unmodifiableSet(mConjuncts);
	}

	@Override
	public String toString() {
		if (getConjuncts().isEmpty()) {
			return "true";
		} else if (getConjuncts().size() == 1) {
			return getConjuncts().iterator().next().toString();
		} else {
			return String.format("(and %s)",
					mConjuncts.stream().map(Object::toString).collect(Collectors.joining(" ")));
		}
	}

}