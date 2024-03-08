/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

public class Configuration<S> {
	private final ImmutableList<S> mStates;

	public Configuration(final ImmutableList<S> states) {
		mStates = states;
	}

	public boolean contains(final S predecessor) {
		return mStates.contains(predecessor);
	}

	public int size() {
		return mStates.size();
	}

	public S get(final int i) {
		return mStates.get(i);
	}

	public Configuration<S> replace(final int i, final S successor) {
		final var list = IntStream.range(0, mStates.size()).mapToObj(j -> j == i ? successor : get(j))
				.collect(Collectors.toList());
		return new Configuration<>(new ImmutableList<>(list));
	}

	public Configuration<S> replace(final Map<Integer, S> subst) {
		final var list = IntStream.range(0, mStates.size()).mapToObj(j -> subst.getOrDefault(j, get(j)))
				.collect(Collectors.toList());
		return new Configuration<>(new ImmutableList<>(list));
	}

	@Override
	public int hashCode() {
		return Objects.hash(mStates);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Configuration other = (Configuration) obj;
		return Objects.equals(mStates, other.mStates);
	}

	@Override
	public String toString() {
		return mStates.toString();
	}

	public Stream<S> stream() {
		return mStates.stream();
	}
}
