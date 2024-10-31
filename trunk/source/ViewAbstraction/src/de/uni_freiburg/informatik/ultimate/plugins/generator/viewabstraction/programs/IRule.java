/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public interface IRule<C> {
	default List<C> successors(final C config) {
		return possibleInstances(config).flatMap(instance -> successors(config, instance)).collect(Collectors.toList());
	}

	Stream<RuleInstantiation> possibleInstances(C configuration);

	Stream<C> successors(C configuration, RuleInstantiation instance);

	int extensionSize();

	default boolean isSpecRule() {
		return false;
	}

	public class RuleInstantiation {
		// TODO replace int by a semantically meaningful type
		private final int[] mThreads;

		public RuleInstantiation(final int thread) {
			this(new int[] { thread });
		}

		public RuleInstantiation(final int[] threads) {
			mThreads = threads;
		}

		public int[] getThreads() {
			return mThreads;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + Arrays.hashCode(mThreads);
			return result;
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
			final RuleInstantiation other = (RuleInstantiation) obj;
			return Arrays.equals(mThreads, other.mThreads);
		}

		@Override
		public String toString() {
			return "RuleInstantiation [mThreads=" + Arrays.toString(mThreads) + "]";
		}
	}
}
