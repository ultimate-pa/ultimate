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
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.por;

import java.util.List;
import java.util.function.IntPredicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramConfiguration;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepReducedProgram {
	public static <S> Program<Configuration<Pair<S, Boolean>>> reduce(final Program<Configuration<S>> program,
			final IIndependenceRelation<?, IRule<Configuration<S>>> commutativity) {
		final List<IRule<Configuration<Pair<S, Boolean>>>> reducedRules = program.getRules().stream()
				.map(r -> new ReducedRule<>(r, commutativity, program)).collect(Collectors.toList());
		return new Program<>(reducedRules);
	}

	public static <S, T> Program<ProgramConfiguration<S, Pair<T, Boolean>>> reduceWithGlobals(
			final Program<ProgramConfiguration<S, T>> program,
			final IIndependenceRelation<?, IRule<ProgramConfiguration<S, T>>> commutativity) {
		final List<IRule<ProgramConfiguration<S, Pair<T, Boolean>>>> reducedRules = program.getRules().stream()
				.map(r -> new ReducedProgramRule<>(r, commutativity, program)).collect(Collectors.toList());
		return new Program<>(reducedRules);
	}

	private static class ReducedRule<S> implements IRule<Configuration<Pair<S, Boolean>>> {
		private final IRule<Configuration<S>> mUnderlying;
		private final IIndependenceRelation<?, IRule<Configuration<S>>> mIndependence;
		private final Program<Configuration<S>> mProgram;

		public ReducedRule(final IRule<Configuration<S>> underlying,
				final IIndependenceRelation<?, IRule<Configuration<S>>> independence,
				final Program<Configuration<S>> program) {
			mUnderlying = underlying;
			mIndependence = independence;
			mProgram = program;
		}

		@Override
		public boolean isApplicable(final Configuration<Pair<S, Boolean>> config) {
			final var original = underlying(config);
			if (!mUnderlying.isApplicable(original)) {
				return false;
			}
			final var succs = mUnderlying.successors(original);
			return succs.stream().anyMatch(s -> active(original, s).noneMatch(i -> config.getThread(i).getSecond()));
		}

		@Override
		public List<Configuration<Pair<S, Boolean>>> successors(final Configuration<Pair<S, Boolean>> config) {
			final var original = underlying(config);
			final var succs = mUnderlying.successors(original);
			return succs.stream().filter(s -> active(original, s).noneMatch(i -> config.getThread(i).getSecond()))
					.map(s -> updateSleep(config, s, active(original, s))).collect(Collectors.toList());
		}

		@Override
		public int extensionSize() {
			return mUnderlying.extensionSize();
		}

		private Configuration<Pair<S, Boolean>> updateSleep(final Configuration<Pair<S, Boolean>> previous,
				final Configuration<S> config, final IntStream active) {
			return SleepReducedProgram.updateSleep(mProgram, mIndependence, mUnderlying, underlying(previous),
					i -> previous.getThread(i).getSecond(), config, active);
		}
	}

	private static class ReducedProgramRule<S, T> implements IRule<ProgramConfiguration<S, Pair<T, Boolean>>> {
		private final IRule<ProgramConfiguration<S, T>> mUnderlying;
		private final IIndependenceRelation<?, IRule<ProgramConfiguration<S, T>>> mIndependence;
		private final Program<ProgramConfiguration<S, T>> mProgram;

		public ReducedProgramRule(final IRule<ProgramConfiguration<S, T>> underlying,
				final IIndependenceRelation<?, IRule<ProgramConfiguration<S, T>>> independence,
				final Program<ProgramConfiguration<S, T>> program) {
			mUnderlying = underlying;
			mIndependence = independence;
			mProgram = program;
		}

		@Override
		public boolean isApplicable(final ProgramConfiguration<S, Pair<T, Boolean>> config) {
			final var original = underlyingProgramConfig(config);
			if (!mUnderlying.isApplicable(original)) {
				return false;
			}
			final var succs = mUnderlying.successors(original);
			return succs.stream().anyMatch(s -> active(original, s).noneMatch(i -> config.getThread(i).getSecond()));
		}

		@Override
		public List<ProgramConfiguration<S, Pair<T, Boolean>>>
				successors(final ProgramConfiguration<S, Pair<T, Boolean>> config) {
			final var original = underlyingProgramConfig(config);
			final var succs = mUnderlying.successors(original);
			return succs.stream().filter(s -> active(original, s).noneMatch(i -> config.getThread(i).getSecond()))
					.map(s -> updateSleep(config, s, active(original, s))).collect(Collectors.toList());
		}

		@Override
		public int extensionSize() {
			return mUnderlying.extensionSize();
		}

		private ProgramConfiguration<S, Pair<T, Boolean>> updateSleep(
				final ProgramConfiguration<S, Pair<T, Boolean>> previous, final ProgramConfiguration<S, T> config,
				final IntStream active) {
			final var newThreads = SleepReducedProgram.<T, ProgramConfiguration<S, T>> updateSleep(mProgram,
					mIndependence, mUnderlying, underlyingProgramConfig(previous),
					i -> previous.getThread(i).getSecond(), config, active);
			return new ProgramConfiguration<>(config.getControllerState(), newThreads);
		}

		@Override
		public String toString() {
			return "sleep<" + mUnderlying.toString() + ">";
		}
	}

	private static <S, C extends IThreadBasedConfiguration<S, C>> Configuration<Pair<S, Boolean>> updateSleep(
			final Program<C> program, final IIndependenceRelation<?, IRule<C>> independence, final IRule<C> action,
			final C previous, final IntPredicate previousSleep, final C config, final IntStream active) {
		final int maxActive = active.max().getAsInt();
		ImmutableList<Pair<S, Boolean>> newThreads = ImmutableList.empty();
		for (int i = config.numberOfThreads() - 1; i >= 0; --i) {
			final boolean asleep;
			if (i < maxActive || previousSleep.test(i)) {
				asleep = enabled(program, previous, i).filter(r -> !r.isSpecRule())
						.allMatch(r -> independence.isIndependent(null, action, r) == Dependence.INDEPENDENT);
			} else {
				asleep = false;
			}

			newThreads = new ImmutableList<>(new Pair<>(config.getThread(i), asleep), newThreads);
		}
		return new Configuration<>(newThreads);
	}

	private static <C extends IThreadBasedConfiguration<?, C>> Stream<? extends IRule<C>>
			enabled(final Program<C> program, final C config, final int i) {
		return program.getRules().stream().filter(r -> r.isApplicable(config))
				.filter(r -> r.successors(config).stream().anyMatch(s -> active(config, s).anyMatch(j -> j == i)));
	}

	private static <C extends IThreadBasedConfiguration<?, C>> IntStream active(final C original, final C succ) {
		return IntStream.range(0, original.numberOfThreads()).filter(i -> original.getThread(i) != succ.getThread(i));
	}

	public static <X> Configuration<X> underlying(final Configuration<Pair<X, Boolean>> config) {
		return new Configuration<>(
				new ImmutableList<>(config.stream().map(Pair::getFirst).collect(Collectors.toList())));
	}

	public static <S, T> ProgramConfiguration<S, T>
			underlyingProgramConfig(final ProgramConfiguration<S, Pair<T, Boolean>> config) {
		return new ProgramConfiguration<>(config.getControllerState(), underlying(config.getThreadConfiguration()));
	}

	public static <X> Configuration<Pair<X, Boolean>> wrapInitial(final Configuration<X> initial) {
		return new Configuration<>(
				new ImmutableList<>(initial.stream().map(s -> new Pair<>(s, false)).collect(Collectors.toList())));
	}

	public static <S, T> ProgramConfiguration<S, Pair<T, Boolean>>
			wrapInitialProgramConfig(final ProgramConfiguration<S, T> initial) {
		return new ProgramConfiguration<>(initial.getControllerState(), wrapInitial(initial.getThreadConfiguration()));
	}
}
