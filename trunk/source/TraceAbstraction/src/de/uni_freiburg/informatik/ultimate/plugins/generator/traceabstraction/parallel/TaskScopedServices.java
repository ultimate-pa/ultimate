/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * The services of one task of a worker, e.g. one counterexample check. Everything comes from the worker's services,
 * except that the storage remembers what the task puts into it, so that {@link #destroyAll(ILogger)} destroys exactly
 * that once the task is done: above all the solvers of the task's trace checks, each of which is an external process.
 * <p>
 * The sequential CEGAR loop does the same with one marker of the toolchain storage per iteration
 * ({@link IToolchainStorage#pushMarker(Object)}). The workers cannot use markers: the marker stack belongs to the whole
 * toolchain, and the main thread and the other workers put storables into it at the same time. Without this, every
 * checked counterexample left a solver process running until the end of the CEGAR loop.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class TaskScopedServices implements IUltimateServiceProvider {

	private final IUltimateServiceProvider mParent;
	private final TaskStorage mStorage;

	public TaskScopedServices(final IUltimateServiceProvider parent) {
		this(parent, new TaskStorage(parent.getStorage()));
	}

	private TaskScopedServices(final IUltimateServiceProvider parent, final TaskStorage storage) {
		mParent = Objects.requireNonNull(parent);
		mStorage = storage;
	}

	/**
	 * Destroys every storable the task put into the storage and did not remove itself, newest first, as the toolchain
	 * storage does: a script is destroyed before the solver process it runs on.
	 *
	 * @return how many storables were destroyed
	 */
	public int destroyAll(final ILogger logger) {
		return mStorage.destroyAll(logger);
	}

	@Override
	public IToolchainStorage getStorage() {
		return mStorage;
	}

	@Override
	public IBacktranslationService getBacktranslationService() {
		return mParent.getBacktranslationService();
	}

	@Override
	public ILoggingService getLoggingService() {
		return mParent.getLoggingService();
	}

	@Override
	public IResultService getResultService() {
		return mParent.getResultService();
	}

	@Override
	public IProgressMonitorService getProgressMonitorService() {
		// Its child timers wrap this provider, so they keep the task storage.
		return mParent.getProgressMonitorService();
	}

	@Override
	public <T extends IService, K extends IServiceFactory<T>> T getServiceInstance(final Class<K> serviceType) {
		return mParent.getServiceInstance(serviceType);
	}

	@Override
	public IPreferenceProvider getPreferenceProvider(final String pluginId) {
		return mParent.getPreferenceProvider(pluginId);
	}

	@Override
	public IUltimateServiceProvider registerPreferenceLayer(final Class<?> creator, final String... pluginIds) {
		return new TaskScopedServices(mParent.registerPreferenceLayer(creator, pluginIds), mStorage);
	}

	@Override
	public IUltimateServiceProvider registerDefaultPreferenceLayer(final Class<?> creator, final String... pluginIds) {
		return new TaskScopedServices(mParent.registerDefaultPreferenceLayer(creator, pluginIds), mStorage);
	}

	/**
	 * The toolchain storage, which in addition records the keys put through it. Solver processes remove themselves from
	 * their own threads when they end, so the record is synchronized.
	 */
	private static final class TaskStorage implements IToolchainStorage {

		private final IToolchainStorage mParent;
		private final Set<String> mKeys = new LinkedHashSet<>();

		TaskStorage(final IToolchainStorage parent) {
			mParent = Objects.requireNonNull(parent);
		}

		int destroyAll(final ILogger logger) {
			final List<String> keys;
			synchronized (mKeys) {
				keys = new ArrayList<>(mKeys);
				mKeys.clear();
			}
			Collections.reverse(keys);
			int destroyed = 0;
			for (final String key : keys) {
				try {
					if (mParent.destroyStorable(key)) {
						destroyed++;
					}
				} catch (final Throwable t) {
					// A solver that is already dead cannot be told to exit; its process is gone anyway.
					logger.debug("Could not destroy %s: %s", key, t);
				}
			}
			return destroyed;
		}

		@Override
		public boolean destroyStorable(final String key) {
			synchronized (mKeys) {
				mKeys.remove(key);
			}
			return mParent.destroyStorable(key);
		}

		@Override
		public IStorable removeStorable(final String key) {
			synchronized (mKeys) {
				mKeys.remove(key);
			}
			return mParent.removeStorable(key);
		}

		@Override
		public IStorable getStorable(final String key) {
			return mParent.getStorable(key);
		}

		@Override
		public IStorable putStorable(final String key, final IStorable value) {
			synchronized (mKeys) {
				mKeys.add(key);
			}
			return mParent.putStorable(key, value);
		}

		@Override
		public void clear() {
			// Only what this task put there, never the storables of the rest of the toolchain.
			throw new UnsupportedOperationException("a task storage cannot clear the toolchain storage");
		}

		@Override
		public Set<String> keys() {
			synchronized (mKeys) {
				return new LinkedHashSet<>(mKeys);
			}
		}

		@Override
		public void pushMarker(final Object marker) {
			mParent.pushMarker(marker);
		}

		@Override
		public Set<String> destroyMarker(final Object marker) {
			return mParent.destroyMarker(marker);
		}
	}
}
