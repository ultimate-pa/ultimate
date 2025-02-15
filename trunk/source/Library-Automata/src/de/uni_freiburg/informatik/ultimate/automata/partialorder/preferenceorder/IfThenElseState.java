/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder;

import java.util.Objects;

/**
 * Represents a generalization of {@code Either} that allows an instance to not contain a value at all.
 */
public sealed interface IfThenElseState<X, Y> {
	record Then<X, Y>(X value) implements IfThenElseState<X, Y> {
		@Override
		public int hashCode() {
			// Override hashCode() such that Then(x) and Else(x) hash differently
			return Objects.hash(17, value);
		}

		@Override
		public String toString() {
			return "Then[" + value + "]";
		}
	}

	record Else<X, Y>(Y value) implements IfThenElseState<X, Y> {
		@Override
		public int hashCode() {
			// Override hashCode() such that Then(x) and Else(x) hash differently
			return Objects.hash(23, value);
		}

		@Override
		public String toString() {
			return "Else[" + value + "]";
		}
	}

	record Initial<X, Y>() implements IfThenElseState<X, Y> {
		// We no longer have a value, so the class needs to be entirely empty.
	}
}
