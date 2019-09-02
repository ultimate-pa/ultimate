/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.model.preferences;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IPreferenceProvider {

	boolean getBoolean(String key);

	boolean getBoolean(String key, boolean defaultValue);

	String getString(String key);

	String getString(String key, String defaultValue);

	<T extends Enum<T>> T getEnum(String key, Class<T> clazz);

	<T extends Enum<T>> T getEnum(String key, T defaultValue, Class<T> clazz);

	byte[] getByteArray(String key);

	byte[] getByteArray(String key, byte[] defaultValue);

	double getDouble(String key);

	double getDouble(String key, double defaultValue);

	float getFloat(String key);

	float getFloat(String key, float defaultValue);

	int getInt(String key);

	int getInt(String key, int defaultValue);

	long getLong(String key);

	long getLong(String key, long defaultValue);

	void put(String key, String value);

	void put(String key, Object value);

	/**
	 * * @return All settings represented by this preference provider on a single line.
	 */
	String getSingleLinePreferenceString();

}
