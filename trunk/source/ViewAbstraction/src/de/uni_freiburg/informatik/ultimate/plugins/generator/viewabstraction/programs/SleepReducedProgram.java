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

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepReducedProgram {
	public static <X> Program<Pair<X, Boolean>> reduce(final Program<X> program,
			final IIndependenceRelation<?, IRule<X>> commutativity) {
		final List<IRule<Pair<X, Boolean>>> reducedRules = program.getRules().stream()
				.map(r -> new ReducedRule<>(r, commutativity, program)).collect(Collectors.toList());
		return new Program<>(null, reducedRules);

	}

	private static class ReducedRule<X> implements IRule<Pair<X, Boolean>> {
		private final IRule<X> mUnderlying;
		private final IIndependenceRelation<?, IRule<X>> mIndependence;
		private final Program<X> mProgram;

		public ReducedRule(final IRule<X> underlying, final IIndependenceRelation<?, IRule<X>> independence,
				final Program<X> program) {
			mUnderlying = underlying;
			mIndependence = independence;
			mProgram = program;
		}

		@Override
		public boolean isApplicable(final Configuration<Pair<X, Boolean>> config) {
			final var original = underlying(config);
			if (!mUnderlying.isApplicable(original)) {
				return false;
			}
			final var succs = mUnderlying.successors(original);
			return succs.stream().anyMatch(s -> active(original, s).noneMatch(i -> config.get(i).getSecond()));
		}

		@Override
		public List<Configuration<Pair<X, Boolean>>> successors(final Configuration<Pair<X, Boolean>> config) {
			final var original = underlying(config);
			final var succs = mUnderlying.successors(original);
			return succs.stream().filter(s -> active(original, s).noneMatch(i -> config.get(i).getSecond()))
					.map(s -> updateSleep(config, s, active(original, s))).collect(Collectors.toList());
		}

		@Override
		public int extensionSize() {
			return mUnderlying.extensionSize();
		}

		private Configuration<Pair<X, Boolean>> updateSleep(final Configuration<Pair<X, Boolean>> previous,
				final Configuration<X> config, final IntStream active) {
			final int maxActive = active.max().getAsInt();
			return new Configuration<>(new ImmutableList<>(IntStream.range(0, config.size())
					.mapToObj(i -> new Pair<>(config.get(i), (i < maxActive || previous.get(i).getSecond())
							&& enabled(mProgram, underlying(previous), i).allMatch(
									r -> mIndependence.isIndependent(null, r, mUnderlying) == Dependence.INDEPENDENT)))
					.collect(Collectors.toList())));
		}
	}

	private static <X> Stream<? extends IRule<X>> enabled(final Program<X> program, final Configuration<X> config,
			final int i) {
		return program.getRules().stream().filter(r -> r.isApplicable(config))
				.filter(r -> r.successors(config).stream().anyMatch(s -> active(config, s).anyMatch(j -> j == i)));
	}

	private static <X> IntStream active(final Configuration<X> original, final Configuration<X> succ) {
		return IntStream.range(0, original.size()).filter(i -> original.get(i) != succ.get(i));
	}

	public static <X> Configuration<X> underlying(final Configuration<Pair<X, Boolean>> config) {
		return new Configuration<>(
				new ImmutableList<>(config.stream().map(Pair::getFirst).collect(Collectors.toList())));
	}
}
