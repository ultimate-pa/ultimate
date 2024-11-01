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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.function.IntPredicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule.RuleInstantiation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramConfiguration;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetReduction<C, CS> {
	private final Map<IRule<C>, IRule<CS>> mEdgeMap = new HashMap<>();
	private final Program<CS> mProgram;

	private SleepSetReduction(final Program<C> program, final IIndependenceRelation<?, IRule<C>> independence,
			final IRuleFactory<C, CS> factory) {
		final var reducedRules = new ArrayList<IRule<CS>>();
		for (final var rule : program.getRules()) {
			final var reducedRule = factory.makeRule(rule, independence, program);
			mEdgeMap.put(rule, reducedRule);
			reducedRules.add(reducedRule);
		}
		mProgram = new Program<>(reducedRules);
	}

	public Program<CS> getProgram() {
		return mProgram;
	}

	public IRule<CS> getReducedRule(final IRule<C> rule) {
		return mEdgeMap.get(rule);
	}

	private interface IRuleFactory<C, CS> {
		IRule<CS> makeRule(IRule<C> rule, IIndependenceRelation<?, IRule<C>> independence, Program<C> program);
	}

	public static <S> Program<Configuration<Pair<S, Boolean>>> reduce(final Program<Configuration<S>> program,
			final IIndependenceRelation<?, IRule<Configuration<S>>> commutativity) {
		return new SleepSetReduction<>(program, commutativity, ReducedRule::new).getProgram();
	}

	public static <S, T> SleepSetReduction<ProgramConfiguration<S, T>, ProgramConfiguration<S, Pair<T, Boolean>>>
			reduceWithGlobals(final Program<ProgramConfiguration<S, T>> program,
					final IIndependenceRelation<?, IRule<ProgramConfiguration<S, T>>> commutativity) {
		return new SleepSetReduction<>(program, commutativity, ReducedProgramRule::new);
	}

	public static class ReducedRule<S> implements IRule<Configuration<Pair<S, Boolean>>> {
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
		public Stream<RuleInstantiation> possibleInstances(final Configuration<Pair<S, Boolean>> configuration) {
			final var original = underlying(configuration);
			return mUnderlying.possibleInstances(original).filter(instance -> !isSleepBlocked(configuration, instance));
		}

		@Override
		public Stream<Configuration<Pair<S, Boolean>>> successors(final Configuration<Pair<S, Boolean>> configuration,
				final RuleInstantiation instance) {
			assert !isSleepBlocked(configuration, instance);
			final var original = underlying(configuration);
			return mUnderlying.successors(original, instance)
					.map(s -> updateSleep(configuration, s, instance.getThreads()));
		}

		@Override
		public int extensionSize() {
			return mUnderlying.extensionSize();
		}

		private Configuration<Pair<S, Boolean>> updateSleep(final Configuration<Pair<S, Boolean>> previous,
				final Configuration<S> config, final int[] active) {
			return SleepSetReduction.updateSleep(mProgram, mIndependence, mUnderlying, underlying(previous),
					i -> previous.getThread(i).getSecond(), config, active);
		}
	}

	public static class ReducedProgramRule<S, T> implements IRule<ProgramConfiguration<S, Pair<T, Boolean>>> {
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
		public Stream<RuleInstantiation>
				possibleInstances(final ProgramConfiguration<S, Pair<T, Boolean>> configuration) {
			final var original = underlyingProgramConfig(configuration);
			return mUnderlying.possibleInstances(original).filter(instance -> !isSleepBlocked(configuration, instance));
		}

		@Override
		public Stream<ProgramConfiguration<S, Pair<T, Boolean>>> successors(
				final ProgramConfiguration<S, Pair<T, Boolean>> configuration, final RuleInstantiation instance) {
			assert !isSleepBlocked(configuration, instance);
			final var original = underlyingProgramConfig(configuration);
			return mUnderlying.successors(original, instance)
					.map(s -> updateSleep(configuration, s, instance.getThreads()));
		}

		private boolean isSleepBlocked(final ProgramConfiguration<S, Pair<T, Boolean>> configuration,
				final RuleInstantiation instance) {
			return SleepSetReduction.isSleepBlocked(configuration.getThreadConfiguration(), instance);
		}

		@Override
		public int extensionSize() {
			return mUnderlying.extensionSize();
		}

		private ProgramConfiguration<S, Pair<T, Boolean>> updateSleep(
				final ProgramConfiguration<S, Pair<T, Boolean>> previous, final ProgramConfiguration<S, T> config,
				final int[] active) {
			final var newThreads = SleepSetReduction.<T, ProgramConfiguration<S, T>> updateSleep(mProgram,
					mIndependence, mUnderlying, underlyingProgramConfig(previous),
					i -> previous.getThread(i).getSecond(), config, active);
			return new ProgramConfiguration<>(config.getControllerState(), newThreads);
		}

		@Override
		public String toString() {
			return "sleep<" + mUnderlying.toString() + ">";
		}
	}

	private static <S> boolean isSleepBlocked(final Configuration<Pair<S, Boolean>> configuration,
			final RuleInstantiation ruleInstance) {
		return Arrays.stream(ruleInstance.getThreads()).anyMatch(i -> configuration.getThread(i).getSecond());
	}

	private static <S, C extends IThreadBasedConfiguration<S, C>> Configuration<Pair<S, Boolean>> updateSleep(
			final Program<C> program, final IIndependenceRelation<?, IRule<C>> independence, final IRule<C> action,
			final C previous, final IntPredicate previousSleep, final C config, final int[] active) {
		final int maxActive = Arrays.stream(active).max().getAsInt();
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
		return program.getRules().stream()
				.filter(r -> r.possibleInstances(config).filter(instance -> involves(instance, i))
						.flatMap(instance -> r.successors(config, instance)).findAny().isPresent());
	}

	private static boolean involves(final RuleInstantiation instance, final int thread) {
		return Arrays.stream(instance.getThreads()).anyMatch(i -> i == thread);
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
