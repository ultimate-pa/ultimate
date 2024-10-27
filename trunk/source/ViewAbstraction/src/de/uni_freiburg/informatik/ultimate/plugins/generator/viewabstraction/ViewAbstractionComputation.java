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

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.abstractdomain.IViewAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;

public class ViewAbstractionComputation<C, V> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IViewAbstraction<C, V> mViewAbstraction;
	private final int mLevel;

	private final Program<C> mProgram;
	private final int mDelta;

	private final IObserver<V> mObserver;

	private final Set<V> mCurrent;
	private final Set<V> mNewViews = new LinkedHashSet<>();
	private final Set<C> mConsideredConfigs = new HashSet<>();

	private Status mStatus = Status.PAUSED;
	private int mIteration = 0;

	public enum Status {
		PAUSED, COMPLETED, CANCELLED
	}

	public ViewAbstractionComputation(final IUltimateServiceProvider services,
			final IViewAbstraction<C, V> viewAbstraction, final int level, final Program<C> program,
			final Set<V> initial) {
		this(services, viewAbstraction, level, program, initial, null);
	}

	public ViewAbstractionComputation(final IUltimateServiceProvider services,
			final IViewAbstraction<C, V> viewAbstraction, final int level, final Program<C> program,
			final Set<V> initial, final IObserver<V> observer) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());

		mViewAbstraction = viewAbstraction;
		mLevel = level;

		mProgram = program;
		mDelta = program.getExtensionSize();

		mObserver = observer;

		mCurrent = new LinkedHashSet<>(initial);
		mNewViews.addAll(initial);
	}

	public Set<V> getCurrentAbstraction() {
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
			final var nextViews = abstractPost(mCurrent);
			mNewViews.clear();
			for (final var view : nextViews) {
				final boolean isNew = mCurrent.add(view);
				changed = changed || isNew;
				if (isNew) {
					mNewViews.add(view);
					mLogger.debug("new view: %s", view);

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
			mLogger.debug("views: %s", mCurrent);

			if (!mServices.getProgressMonitorService().continueProcessing()) {
				mStatus = changed ? Status.CANCELLED : Status.COMPLETED;
				throw new ToolchainCanceledException(getClass());
			}
		} while (changed && (maxIterations < 0 || localIterations <= maxIterations));

		mStatus = changed ? Status.PAUSED : Status.COMPLETED;
		mLogger.info("fixpoint algorithm %s after %d iterations", mStatus, mIteration);
		return mStatus;
	}

	private Set<V> abstractPost(final Set<V> views) {
		final var extended = mViewAbstraction.concretizeFromViews(views, mLevel, mLevel + mDelta);
		mLogger.debug("extended %d views of size %d by delta=%d to %d configurations", views.size(), mLevel, mDelta,
				extended.size());

		// TODO rather than post-hoc filtering, only generated extended configs with at least one new view
		final var filteredExt = extended.stream()
				.filter(c -> mViewAbstraction.abstractAsViews(c, mLevel).stream().anyMatch(mNewViews::contains))
				.collect(Collectors.toCollection(LinkedHashSet::new));
		mLogger.debug("filtered configurations %d configurations have new views", filteredExt.size());

		final var post = concretePost(filteredExt);
		mLogger.debug("concrete post of %d extended views had %d configurations", filteredExt.size(), post.size());

		final var abstracted = getViews(post);
		mLogger.debug("abstraction yielded %d views", abstracted.size());

		return abstracted;
	}

	private Set<C> concretePost(final Set<C> configs) {
		final var result = new LinkedHashSet<>(configs);
		for (final var c : configs) {
			final boolean newConfig = mConsideredConfigs.add(c);
			if (!newConfig) {
				continue;
			}

			mLogger.debug("considering successors for configuration %s", c);
			for (final var rule : mProgram.getRules()) {
				if (rule.isApplicable(c)) {
					final var successors = rule.successors(c);
					mLogger.debug("  successors for rule %s: %s", rule, successors);
					result.addAll(successors);
				}
			}
		}
		return result;
	}

	private Set<V> getViews(final Set<C> configs) {
		return configs.stream().flatMap(c -> mViewAbstraction.abstractAsViews(c, mLevel).stream())
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}

	private boolean observe(final V newView) {
		if (mObserver == null) {
			return false;
		}
		return mObserver.observe(newView);
	}

	public interface IObserver<V> {
		boolean observe(V newView);
	}
}
