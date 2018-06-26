/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;

/**
 * A {@link PreferenceLayer} instance allows you to supplement preference provider with your own preferences at runtime.
 * This can be useful in implementing both, user-configured and program-configured algorithms.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PreferenceLayer implements IPreferenceProvider {

	private final IPreferenceProvider mBacking;
	private final Map<String, Object> mPreferenceOverlay;
	private final Class<?> mCreator;

	/**
	 * Create a new preference layer over some {@link IPreferenceProvider}.
	 *
	 * @param backing
	 *            The given {@link IPreferenceProvider}
	 * @param creator
	 *            The creator of this layer (for debugging purposes)
	 */
	public PreferenceLayer(final IPreferenceProvider backing, final Class<?> creator) {
		mBacking = Objects.requireNonNull(backing);
		mPreferenceOverlay = new HashMap<>();
		mCreator = Objects.requireNonNull(creator);
	}

	@Override
	public boolean getBoolean(final String key) {
		return getFromOverlay(key, Boolean::parseBoolean, mBacking::getBoolean);
	}

	@Override
	public boolean getBoolean(final String key, final boolean defaultValue) {
		return getFromOverlay(key, Boolean::parseBoolean, a -> mBacking.getBoolean(a, defaultValue));
	}

	@Override
	public String getString(final String key) {
		return getFromOverlay(key, t -> t, mBacking::getString);
	}

	@Override
	public String getString(final String key, final String defaultValue) {
		return getFromOverlay(key, t -> t, a -> mBacking.getString(a, defaultValue));
	}

	@Override
	public <T extends Enum<T>> T getEnum(final String key, final Class<T> clazz) {
		return getFromOverlay(key, a -> Enum.valueOf(clazz, a), a -> mBacking.getEnum(a, clazz));
	}

	@Override
	public <T extends Enum<T>> T getEnum(final String key, final T defaultValue, final Class<T> clazz) {
		return getFromOverlay(key, a -> Enum.valueOf(clazz, a), a -> mBacking.getEnum(a, defaultValue, clazz));
	}

	@Override
	public byte[] getByteArray(final String key) {
		return getFromOverlay(key, a -> a.getBytes(), mBacking::getByteArray);
	}

	@Override
	public byte[] getByteArray(final String key, final byte[] defaultValue) {
		return getFromOverlay(key, a -> a.getBytes(), a -> mBacking.getByteArray(a, defaultValue));
	}

	@Override
	public double getDouble(final String key) {
		return getFromOverlay(key, Double::parseDouble, mBacking::getDouble);
	}

	@Override
	public double getDouble(final String key, final double defaultValue) {
		return getFromOverlay(key, Double::parseDouble, a -> mBacking.getDouble(a, defaultValue));
	}

	@Override
	public float getFloat(final String key) {
		return getFromOverlay(key, Float::parseFloat, mBacking::getFloat);
	}

	@Override
	public float getFloat(final String key, final float defaultValue) {
		return getFromOverlay(key, Float::parseFloat, a -> mBacking.getFloat(a, defaultValue));
	}

	@Override
	public int getInt(final String key) {
		return getFromOverlay(key, Integer::parseInt, mBacking::getInt);
	}

	@Override
	public int getInt(final String key, final int defaultValue) {
		return getFromOverlay(key, Integer::parseInt, a -> mBacking.getInt(a, defaultValue));
	}

	@Override
	public long getLong(final String key) {
		return getFromOverlay(key, Long::parseLong, mBacking::getLong);
	}

	@Override
	public long getLong(final String key, final long defaultValue) {
		return getFromOverlay(key, Long::parseLong, a -> mBacking.getLong(a, defaultValue));
	}

	@Override
	public void put(final String key, final String value) {
		put(key, (Object) value);
	}

	@Override
	public void put(final String key, final Object value) {
		mPreferenceOverlay.put(key, value);
	}

	@SuppressWarnings("unchecked")
	private <T> T getFromOverlay(final String key, final Function<String, T> funStrToValue,
			final Function<String, T> funFromBacking) {
		final Object value = mPreferenceOverlay.get(key);
		if (value != null) {
			if (value instanceof String) {
				return funStrToValue.apply((String) value);
			}
			return (T) value;
		}
		return funFromBacking.apply(key);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + " created by " + mCreator.getName() + " with " + mPreferenceOverlay.size()
				+ " entries";
	}

	IPreferenceProvider getBacking() {
		return mBacking;
	}

}
