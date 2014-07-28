package de.uni_freiburg.informatik.ultimate.core.services;

import de.uni_freiburg.informatik.ultimate.core.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchainPlugin;

/**
 * {@link IToolchainStorage} is a toolchain-persistent storage that provides
 * {@link IToolchainPlugin}s with the possibility to store information related
 * to one {@link IToolchain} execution. At the end of the lifetime of a
 * {@link IToolchain}, the core will destroy the storage (i.e. call
 * {@link IStorable#destroy() and clear the storage}.
 * 
 * There you can release all resources that need to be released (e.g. close file
 * handlers).
 * 
 * Ultimate's {@link MonitoredProcess} already uses the
 * {@link IToolchainStorage}, so you don't need to care for that.
 * 
 * @author dietsch
 * 
 */
public interface IToolchainStorage {

	/**
	 * Try to remove a single {@link IStorable} and destroy it by calling
	 * {@link IStorable#destroy()} on it. Possible exceptions should be caught,
	 * logged, and otherwise ignored.
	 * 
	 * @param key
	 *            The key under which the {@link IStorable} is saved.
	 */
	public void destroyStorable(String key);

	/**
	 * Try to remove a single {@link IStorable} and return it.
	 * 
	 * @param key
	 *            The key of the {@link IStorable}.
	 * @return Either the {@link IStorable} that was saved under the key or
	 *         null.
	 */
	public IStorable removeStorable(String key);

	/**
	 * Try to retrieve (not remove) a single {@link IStorable}.
	 * 
	 * @param key
	 *            The key of the {@link IStorable}.
	 * @return Either the {@link IStorable} that is saved under the key or null
	 *         if there is nothing (or null) saved under this key.
	 */
	public IStorable getStorable(String key);

	/**
	 * Save a {@link IStorable} under the given key. If there is already an
	 * {@link IStorable} saved under the key, it will be removed and returned.
	 * 
	 * @param key
	 *            The key under which you want to store your {@link IStorable}.
	 * @param value
	 *            The {@link IStorable}
	 * @return An {@link IStorable} if there was already one in that place or
	 *         null
	 */
	public IStorable putStorable(String key, IStorable value);

	/**
	 * This method clears the {@link IToolchainStorage} and destroys every
	 * {@link IStorable} by calling {@link IStorable#destroy()} on it. Possible
	 * exceptions should be caught, logged, and otherwise ignored.
	 */
	public void clear();

}