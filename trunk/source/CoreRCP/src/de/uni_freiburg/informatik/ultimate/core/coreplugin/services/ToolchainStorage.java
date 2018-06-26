/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
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
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Simple implementation of {@link IToolchainStorage} and {@link IUltimateServiceProvider}
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ToolchainStorage implements IToolchainStorage, IUltimateServiceProvider {

	private final Deque<Pair<Object, Set<String>>> mMarker;
	private final Map<String, IStorable> mToolchainStorage;
	private final Map<String, PreferenceLayer> mPreferenceLayers;

	private final Object mLock;

	public ToolchainStorage() {
		this(new LinkedHashMap<>(), new HashMap<>(), new ArrayDeque<>(), new Object());
		pushMarker(this);
	}

	private ToolchainStorage(final Map<String, IStorable> storage, final Map<String, PreferenceLayer> layers,
			final Deque<Pair<Object, Set<String>>> marker, final Object lock) {
		mLock = Objects.requireNonNull(lock);
		mToolchainStorage = Objects.requireNonNull(storage);
		mPreferenceLayers = Objects.requireNonNull(layers);
		mMarker = Objects.requireNonNull(marker);
	}

	@Override
	public IStorable getStorable(final String key) {
		synchronized (mLock) {
			return mToolchainStorage.get(key);
		}
	}

	@Override
	public IStorable putStorable(final String key, final IStorable value) {
		if (value == null || key == null) {
			throw new IllegalArgumentException("Cannot store nothing");
		}
		synchronized (mLock) {
			final Pair<Object, Set<String>> currentMarker = mMarker.peek();
			currentMarker.getSecond().add(key);
			return mToolchainStorage.put(key, value);
		}
	}

	@Override
	public IStorable removeStorable(final String key) {
		synchronized (mLock) {
			return mToolchainStorage.remove(key);
		}
	}

	@Override
	public void clear() {
		synchronized (mLock) {
			final Collection<IStorable> values = mToolchainStorage.values();
			if (values.isEmpty()) {
				return;
			}
			final List<IStorable> current = new ArrayList<>(values);

			if (current.isEmpty()) {
				return;
			}

			// destroy storables in reverse order s.t., e.g., scripts are destroyed
			// before the solver is destroyed.
			// this is done because we assume that instances created later may
			// depend on instances created earlier.
			Collections.reverse(current);

			final ILogger coreLogger = getLoggingService().getLogger(Activator.PLUGIN_ID);
			if (coreLogger.isDebugEnabled()) {
				coreLogger.debug("Clearing " + current.size() + " storables from " + getClass().getSimpleName());
			}
			for (final IStorable storable : current) {
				if (storable == null) {
					coreLogger.warn("Found NULL storable, ignoring");
					continue;
				}
				try {
					storable.destroy();
				} catch (final Throwable t) {
					if (coreLogger == null) {
						continue;
					}
					coreLogger.fatal("There was an exception during clearing of toolchain storage while destroying "
							+ storable.getClass().toString() + ": " + t.getMessage());
				}
			}
			mToolchainStorage.clear();
			mMarker.clear();
			pushMarker(this);
		}
	}

	@Override
	public boolean destroyStorable(final String key) {
		final IStorable storable = removeStorable(key);
		if (storable != null) {
			storable.destroy();
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return mToolchainStorage.toString();
	}

	@Override
	public IBacktranslationService getBacktranslationService() {
		return BacktranslationService.getService(this);
	}

	@Override
	public ILoggingService getLoggingService() {
		return Log4JLoggingService.getService(this);
		// return Log4J2LoggingService.getService(this);
	}

	@Override
	public IResultService getResultService() {
		return ResultService.getService(this);
	}

	@Override
	public IProgressMonitorService getProgressMonitorService() {
		return ProgressMonitorService.getService(this);
	}

	@Override
	public <T extends IService, K extends IServiceFactory<T>> T getServiceInstance(final Class<K> serviceType) {
		return GenericServiceProvider.getServiceInstance(this, serviceType);
	}

	@Override
	public IPreferenceProvider getPreferenceProvider(final String pluginId) {
		final PreferenceLayer layer = mPreferenceLayers.get(pluginId);
		if (layer != null) {
			return layer;
		}
		return new RcpPreferenceProvider(pluginId);
	}

	@Override
	public IUltimateServiceProvider registerPreferenceLayer(final Class<?> creator, final String... pluginIds) {
		synchronized (mLock) {

			final Map<String, PreferenceLayer> newLayers = new HashMap<>(mPreferenceLayers);
			if (pluginIds == null || pluginIds.length == 0) {
				return this;
			}
			for (final String pluginId : pluginIds) {
				final PreferenceLayer existingLayer = newLayers.get(pluginId);
				final PreferenceLayer newLayer;
				if (existingLayer != null) {
					newLayer = new PreferenceLayer(existingLayer, creator);
				} else {
					newLayer = new PreferenceLayer(getPreferenceProvider(pluginId), creator);
				}
				newLayers.put(pluginId, newLayer);
			}
			return new ToolchainStorage(mToolchainStorage, newLayers, mMarker, mLock);
		}
	}

	@Override
	public IUltimateServiceProvider registerDefaultPreferenceLayer(final Class<?> creator, final String... pluginIds) {
		final IUltimateServiceProvider layer = registerPreferenceLayer(creator, pluginIds);
		for (final String pluginId : pluginIds) {
			final RcpPreferenceProvider prefProvider = new RcpPreferenceProvider(pluginId);
			final IPreferenceProvider preferences = layer.getPreferenceProvider(pluginId);
			for (final Entry<String, Object> entry : prefProvider.getDefaultPreferences().entrySet()) {
				preferences.put(entry.getKey(), entry.getValue());
			}
		}
		return layer;
	}

	@Override
	public Set<String> keys() {
		final Set<String> keys;
		synchronized (mLock) {
			keys = new HashSet<>(mToolchainStorage.keySet());
		}
		return keys;
	}

	@Override
	public void pushMarker(final Object marker) throws IllegalArgumentException {
		if (marker == null) {
			throw new IllegalArgumentException("marker may not be null");
		}
		if (hasMarker(marker)) {
			throw new IllegalArgumentException("duplicate marker");
		}
		synchronized (mLock) {
			mMarker.push(new Pair<>(marker, new HashSet<>()));
		}
	}

	@Override
	public Set<String> destroyMarker(final Object marker) {
		if (mMarker.isEmpty() || !hasMarker(marker)) {
			return Collections.emptySet();
		}
		synchronized (mLock) {
			final Set<String> rtr = new HashSet<>();
			final Iterator<Pair<Object, Set<String>>> iter = mMarker.iterator();
			while (iter.hasNext()) {
				final Pair<Object, Set<String>> markerPair = iter.next();
				iter.remove();
				for (final String key : markerPair.getSecond()) {
					if (destroyStorable(key)) {
						rtr.add(key);
					}
				}
				if (markerPair.getFirst() == marker) {
					return rtr;
				}
			}
			return rtr;
		}
	}

	private boolean hasMarker(final Object marker) {
		assert marker != null;
		synchronized (mLock) {
			return mMarker.stream().map(a -> a.getFirst()).anyMatch(a -> a == marker);
		}
	}

}
