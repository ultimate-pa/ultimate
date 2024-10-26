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
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState.ControllerState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ViewAbstractionComputation<S> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final Program<S> mProgram;
	private final int mLevel;
	private final IObserver<S> mObserver;

	private final int mDelta;
	private final Set<Configuration<S>> mCurrent;
	private final Set<Configuration<S>> mNewViews = new LinkedHashSet<>();

	private Status mStatus = Status.PAUSED;
	private int mIteration = 0;

	public enum Status {
		PAUSED, COMPLETED, CANCELLED
	}

	public ViewAbstractionComputation(final IUltimateServiceProvider services, final Program<S> program,
			final Set<Configuration<S>> initial, final int level) {
		this(services, program, initial, level, null);
	}

	public ViewAbstractionComputation(final IUltimateServiceProvider services, final Program<S> program,
			final Set<Configuration<S>> initial, final int level, final IObserver<S> observer) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.DEBUG);

		mProgram = program;
		mLevel = level;
		mObserver = observer;

		mCurrent = new LinkedHashSet<>(initial);
		mDelta = program.getRules().stream().mapToInt(IRule::extensionSize).max().orElse(0);
	}

	public Set<Configuration<S>> getCurrentAbstraction() {
		return Collections.unmodifiableSet(mCurrent);
	}

	public int getCurrentIteration() {
		return mIteration;
	}

	public Status getStatus() {
		return mStatus;
	}

	public Status run() {
		return run(-1);
	}

	public Status run(final int maxIterations) {
		if (mStatus == Status.COMPLETED || mStatus == Status.CANCELLED) {
			return mStatus;
		}

		int localIterations = 0;

		boolean changed;
		do {
			changed = false;
			mNewViews.clear();
			final var nextViews = abstractPost(mCurrent, mLevel);
			for (final var view : nextViews) {
				final boolean isNew = mCurrent.add(view);
				changed = changed || isNew;
				if (isNew) {
					mNewViews.add(view);
					// TODO in next iteration, only compute successors of configs that have at least one new view

					final boolean stop = observe(view);
					if (stop) {
						mStatus = Status.CANCELLED;
						return mStatus;
					}
				}
			}

			mIteration++;
			localIterations++;
			mLogger.info("fixpoint iteration %d : %d views", mIteration, mCurrent.size());

			if (!mServices.getProgressMonitorService().continueProcessing()) {
				mStatus = changed ? Status.CANCELLED : Status.COMPLETED;
				throw new ToolchainCanceledException(getClass());
			}
		} while (changed && (maxIterations < 0 || localIterations <= maxIterations));

		mStatus = changed ? Status.PAUSED : Status.COMPLETED;
		mLogger.info("fixpoint algorithm %s after %d iterations", mStatus, mIteration);
		return mStatus;
	}

	private Set<Configuration<S>> abstractPost(final Set<Configuration<S>> views, final int k) {
		final var extended = extend(views, k, mDelta);
		mLogger.debug("extended %d views of size %d by delta=%d to %d views", views.size(), k, mDelta, extended.size());

		final var post = concretePost(extended);
		mLogger.debug("concrete post of %d extended views had %d configurations", extended.size(), post.size());

		final var abstracted = getViews(post, k);
		mLogger.debug("abstraction yielded %d views", abstracted.size());

		return abstracted;
	}

	private Set<Configuration<S>> concretePost(final Set<Configuration<S>> configs) {
		final var result = new LinkedHashSet<>(configs);
		for (final var rule : mProgram.getRules()) {
			for (final var c : configs) {
				if (rule.isApplicable(c)) {
					result.addAll(rule.successors(c));
				}
			}
		}
		return result;
	}

	private Set<Configuration<S>> getViews(final Set<Configuration<S>> configs, final int k) {
		return configs.stream().flatMap(c -> getViews(c, k).stream()).collect(Collectors.toSet());
	}

	private Set<Configuration<S>> getViews(final Configuration<S> config, final int k) {
		final boolean hasController = config.get(0) instanceof ControllerState<?, ?>;
		final int minIndex = hasController ? 1 : 0;

		final var queue = new ArrayDeque<Pair<ImmutableList<S>, Integer>>();
		for (int i = config.size() - 1; i >= minIndex + k - 1; --i) {
			queue.push(new Pair<ImmutableList<S>, Integer>(ImmutableList.empty(), i));
		}

		final var result = new LinkedHashSet<Configuration<S>>();
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

		// mLogger.debug("Views of configuration %s : %s", config, result);
		return result;
	}

	// TODO This is an extremely naive and inefficient implementation that is bound to cause issues later on.
	private Set<Configuration<S>> extend(final Set<Configuration<S>> configs, final int k, final int delta) {
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
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}

	private Stream<ImmutableList<S>> listsOfSize(final Set<S> elements, final int size) {
		if (size == 0) {
			return Stream.of(ImmutableList.empty());
		}
		return listsOfSize(elements, size - 1).flatMap(l -> elements.stream().map(e -> new ImmutableList<>(e, l)));
	}

	private boolean observe(final Configuration<S> newView) {
		if (mObserver == null) {
			return false;
		}
		return mObserver.observe(newView);
	}

	public interface IObserver<S> {
		boolean observe(Configuration<S> newView);
	}
}
