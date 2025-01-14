/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Objects;

/**
 * Represents a generalization of {@code Either} that allows an instance to not contain a value at all.
 */
public sealed interface OptionalEither<X, Y> {
	record Left<X, Y>(X value) implements OptionalEither<X, Y> {
		@Override
		public int hashCode() {
			return Objects.hash(17, value);
		}
	}

	record Right<X, Y>(Y value) implements OptionalEither<X, Y> {
		@Override
		public int hashCode() {
			return Objects.hash(23, value);
		}
	}

	record Neither<X, Y>() implements OptionalEither<X, Y> {
		@Override
		public int hashCode() {
			return Objects.hash(29, value);
		}
	}
}
