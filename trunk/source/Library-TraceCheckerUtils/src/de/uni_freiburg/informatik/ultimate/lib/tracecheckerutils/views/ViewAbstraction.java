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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ProgramState.ControllerState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ViewAbstraction<S> {
	private final ILogger mLogger;

	private final Program<S> mProgram;
	private final int mDelta;

	public ViewAbstraction(final IUltimateServiceProvider services, final Program<S> program) {
		mLogger = services.getLoggingService().getLogger(getClass());

		mProgram = program;
		mDelta = program.getRules().stream().mapToInt(IRule::extensionSize).max().orElse(0);
	}

	public Set<Configuration<S>> computeFixedPoint(final Set<Configuration<S>> initial, final int k) {
		final var current = new HashSet<>(initial);
		int iteration = 0;

		boolean changed;
		do {
			changed = current.addAll(abstractPost(current, k));
			iteration++;
			mLogger.info("fixpoint iteration %d", iteration);
		} while (changed);

		return current;
	}

	public Set<Configuration<S>> abstractPost(final Set<Configuration<S>> views, final int k) {
		final var extended = extend(views, k, mDelta);
		final var post = concretePost(extended);
		return getViews(post, k);
	}

	public Set<Configuration<S>> concretePost(final Set<Configuration<S>> configs) {
		final var result = new HashSet<>(configs);
		for (final var rule : mProgram.getRules()) {
			for (final var c : configs) {
				if (rule.isApplicable(c)) {
					result.addAll(rule.successors(c));
				}
			}
		}
		return result;
	}

	public Set<Configuration<S>> getViews(final Set<Configuration<S>> configs, final int k) {
		return configs.stream().flatMap(c -> getViews(c, k).stream()).collect(Collectors.toSet());
	}

	public Set<Configuration<S>> getViews(final Configuration<S> config, final int k) {
		final boolean hasController = config.get(0) instanceof ControllerState<?, ?>;
		final int minIndex = hasController ? 1 : 0;

		final var queue = new ArrayDeque<Pair<ImmutableList<S>, Integer>>();
		for (int i = config.size() - 1; i >= minIndex + k - 1; --i) {
			queue.push(new Pair<ImmutableList<S>, Integer>(ImmutableList.empty(), i));
		}

		final var result = new HashSet<Configuration<S>>();
		while (!queue.isEmpty()) {
			final var current = queue.pop();
			final var list = current.getFirst();
			final int index = current.getSecond();

			if (list.size() == k) {
				if (hasController) {
					result.add(new Configuration<>(new ImmutableList<>(config.get(0), list)));
				} else {
					result.add(new Configuration<>(list));
				}
				continue;
			}

			assert index >= 0;

			final var next = new ImmutableList<>(config.get(index), list);
			for (int i = index - 1; i >= minIndex + (k - next.size()) - 1; --i) {
				queue.push(new Pair<>(next, i));
			}
		}
		return result;
	}

	// TODO This is an extremely naive and inefficient implementation that is bound to cause issues later on.
	public Set<Configuration<S>> extend(final Set<Configuration<S>> configs, final int k, final int delta) {
		final var states = configs.stream().flatMap(c -> c.stream()).collect(Collectors.toSet());
		final var controllerStates =
				states.stream().filter(s -> s instanceof ControllerState<?, ?>).collect(Collectors.toSet());
		final var threadStates = DataStructureUtils.difference(states, controllerStates);

		final var candidates = listsOfSize(threadStates, k + delta);
		Stream<ImmutableList<S>> augmentedCandidates;
		if (controllerStates.isEmpty()) {
			augmentedCandidates = candidates;
		} else {
			augmentedCandidates =
					candidates.flatMap(c -> controllerStates.stream().map(s -> new ImmutableList<>(s, c)));
		}
		return augmentedCandidates.map(Configuration::new).filter(c -> configs.containsAll(getViews(c, k)))
				.collect(Collectors.toSet());
	}

	private Stream<ImmutableList<S>> listsOfSize(final Set<S> elements, final int size) {
		if (size == 0) {
			return Stream.of(ImmutableList.empty());
		}
		return listsOfSize(elements, size - 1).flatMap(l -> elements.stream().map(e -> new ImmutableList<>(e, l)));
	}
}
