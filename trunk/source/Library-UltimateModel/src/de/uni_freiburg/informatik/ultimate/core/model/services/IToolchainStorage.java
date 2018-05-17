/*
 * Copyright (C) 2014-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.core.model.services;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainPlugin;

/**
 * {@link IToolchainStorage} is a toolchain-persistent storage that provides {@link IToolchainPlugin}s with the
 * possibility to store information related to one {@link IToolchain} execution. At the end of the lifetime of a
 * {@link IToolchain}, the core will destroy the storage (i.e. call {@link IStorable#destroy() and clear the storage}.
 *
 * There you can release all resources that need to be released (e.g. close file handlers).
 *
 * Ultimate's {@link MonitoredProcess} already uses the {@link IToolchainStorage}, so you don't need to care for that.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IToolchainStorage {

	/**
	 * Try to remove a single {@link IStorable} and destroy it by calling {@link IStorable#destroy()} on it. Possible
	 * exceptions should be caught, logged, and otherwise ignored.
	 *
	 * @param key
	 *            The key under which the {@link IStorable} is saved.
	 */
	void destroyStorable(final String key);

	/**
	 * Try to remove a single {@link IStorable} and return it.
	 *
	 * @param key
	 *            The key of the {@link IStorable}.
	 * @return Either the {@link IStorable} that was saved under the key or null.
	 */
	IStorable removeStorable(final String key);

	/**
	 * Try to retrieve (not remove) a single {@link IStorable}.
	 *
	 * @param key
	 *            The key of the {@link IStorable}.
	 * @return Either the {@link IStorable} that is saved under the key or null if there is nothing (or null) saved
	 *         under this key.
	 */
	IStorable getStorable(final String key);

	/**
	 * Save a {@link IStorable} under the given key. If there is already an {@link IStorable} saved under the key, it
	 * will be removed and returned.
	 *
	 * @param key
	 *            The key under which you want to store your {@link IStorable}.
	 * @param value
	 *            The {@link IStorable}
	 * @return An {@link IStorable} if there was already one in that place or null
	 */
	IStorable putStorable(final String key, final IStorable value);

	/**
	 * This method clears the {@link IToolchainStorage} and destroys every {@link IStorable} by calling
	 * {@link IStorable#destroy()} on it. Possible exceptions should be caught, logged, and otherwise ignored.
	 */
	void clear();

	/**
	 * List all keys currently in storage
	 */
	Set<String> keys();

}
