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
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntPredicate;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule.RuleInstance;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramConfiguration;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetReduction<T, C extends IThreadBasedConfiguration<T, C>, CS extends IThreadBasedConfiguration<Pair<T, Boolean>, CS>> {
	private static final boolean CHECK_EXECUTABLE_COMMUTATIVITY_ONLY = true;

	private final Map<IRule<C>, IRule<CS>> mEdgeMap = new HashMap<>();
	private final Program<CS> mProgram;

	private SleepSetReduction(final Program<C> program, final IIndependenceRelation<?, RuleInstance<C>> independence,
			final Function<CS, C> projection, final BiFunction<C, IntPredicate, CS> injectSleep) {
		final var reducedRules = new ArrayList<IRule<CS>>();
		for (final var rule : program.getRules()) {
			final var reducedRule = new SleepRule<>(rule, independence, program, projection, injectSleep);
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

	public static <S> SleepSetReduction<S, Configuration<S>, Configuration<Pair<S, Boolean>>> reduce(
			final Program<Configuration<S>> program,
			final IIndependenceRelation<?, RuleInstance<Configuration<S>>> commutativity) {
		return new SleepSetReduction<>(program, commutativity, SleepSetReduction::underlying,
				SleepSetReduction::injectSleep);
	}

	public static <G, T> SleepSetReduction<T, ProgramConfiguration<G, T>, ProgramConfiguration<G, Pair<T, Boolean>>>
			reduceWithGlobals(final Program<ProgramConfiguration<G, T>> program,
					final IIndependenceRelation<?, RuleInstance<ProgramConfiguration<G, T>>> commutativity) {
		return new SleepSetReduction<>(program, commutativity, SleepSetReduction::underlying,
				SleepSetReduction::injectSleep);
	}

	private static class SleepRule<T, C extends IThreadBasedConfiguration<T, C>, CS extends IThreadBasedConfiguration<Pair<T, Boolean>, CS>>
			implements IRule<CS> {
		private final IRule<C> mUnderlying;
		private final IIndependenceRelation<?, RuleInstance<C>> mIndependence;
		private final Program<C> mProgram;

		private final Function<CS, C> mProjection;
		private final BiFunction<C, IntPredicate, CS> mInjectSleep;

		public SleepRule(final IRule<C> underlying, final IIndependenceRelation<?, RuleInstance<C>> independence,
				final Program<C> program, final Function<CS, C> projection,
				final BiFunction<C, IntPredicate, CS> injectSleep) {
			mUnderlying = underlying;
			mIndependence = independence;
			mProgram = program;
			mProjection = projection;
			mInjectSleep = injectSleep;
		}

		@Override
		public Stream<TransitionProvider<CS>> outgoingTransitions(final CS configuration) {
			return mUnderlying.outgoingTransitions(mProjection.apply(configuration))
					.filter(tp -> !isSleepBlocked(configuration, tp))
					.map(tp -> wrapTransitionProvider(configuration, tp));
		}

		@Override
		public int extensionSize() {
			return mUnderlying.extensionSize();
		}

		private boolean isSleepBlocked(final CS configuration, final TransitionProvider<C> transitionProvider) {
			return Arrays.stream(transitionProvider.getThreads()).anyMatch(i -> configuration.getThread(i).getSecond());
		}

		private TransitionProvider<CS> wrapTransitionProvider(final CS predecessor, final TransitionProvider<C> tp) {
			return new TransitionProvider<>(predecessor, tp.getThreads(),
					tp.getSuccessors().map(succ -> updateSleep(predecessor, tp.getThreads(), succ)));
		}

		private CS updateSleep(final CS predecessor, final int[] threads, final C successorWithoutSleep) {
			final int maxActive = Arrays.stream(threads).max().getAsInt();
			final var predecessorWithoutSleep = mProjection.apply(predecessor);
			final var currentInstance = new RuleInstance<>(mUnderlying, threads);
			final IntPredicate newSleep = i -> {
				return (i < maxActive || predecessor.getThread(i).getSecond())
						&& enabled(predecessorWithoutSleep, i).filter(r -> !r.getRule().isSpecRule()).allMatch(
								r -> mIndependence.isIndependent(null, currentInstance, r) == Dependence.INDEPENDENT);
			};
			return mInjectSleep.apply(successorWithoutSleep, newSleep);
		}

		private Stream<RuleInstance<C>> enabled(final C config, final int thread) {
			final Predicate<TransitionProvider<C>> transitionFilter;
			if (CHECK_EXECUTABLE_COMMUTATIVITY_ONLY) {
				transitionFilter = tp -> involves(tp, thread) && tp.getSuccessors().findAny().isPresent();
			} else {
				transitionFilter = tp -> involves(tp, thread);
			}
			return mProgram.getRules().stream().flatMap(r -> r.outgoingTransitions(config).filter(transitionFilter)
					.map(tp -> new RuleInstance<>(r, tp.getThreads())));
		}

		private boolean involves(final TransitionProvider<C> instance, final int thread) {
			return Arrays.stream(instance.getThreads()).anyMatch(i -> i == thread);
		}
	}

	public static <X> Configuration<X> underlying(final Configuration<Pair<X, Boolean>> config) {
		return new Configuration<>(
				new ImmutableList<>(config.stream().map(Pair::getFirst).collect(Collectors.toList())));
	}

	public static <S, T> ProgramConfiguration<S, T> underlying(final ProgramConfiguration<S, Pair<T, Boolean>> config) {
		return new ProgramConfiguration<>(config.getControllerState(), underlying(config.getThreadConfiguration()));
	}

	private static <G, T> ProgramConfiguration<G, Pair<T, Boolean>> injectSleep(final ProgramConfiguration<G, T> config,
			final IntPredicate sleep) {
		return new ProgramConfiguration<>(config.getControllerState(),
				injectSleep(config.getThreadConfiguration(), sleep));
	}

	private static <S> Configuration<Pair<S, Boolean>> injectSleep(final Configuration<S> config,
			final IntPredicate sleep) {
		final var threadStates = IntStream.range(0, config.numberOfThreads())
				.mapToObj(i -> new Pair<>(config.getThread(i), sleep.test(i)))
				.collect(Collectors.toCollection(ImmutableList::new));
		return new Configuration<>(threadStates);
	}

	public static <X> Configuration<Pair<X, Boolean>> wrapInitial(final Configuration<X> initial) {
		return injectSleep(initial, i -> false);
	}

	public static <S, T> ProgramConfiguration<S, Pair<T, Boolean>>
			wrapInitialProgramConfig(final ProgramConfiguration<S, T> initial) {
		return new ProgramConfiguration<>(initial.getControllerState(), wrapInitial(initial.getThreadConfiguration()));
	}
}
