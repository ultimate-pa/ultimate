/*
 * Copyright (C) 2009-2015 Björn Buchhold
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model.repository
 * File:	IRepository.java created on Oct 28, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.modelrepository;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.DuplicateKeyException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.PersistentObjectNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.PersistentObjectTypeMismatchException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;

/**
 * Repository interface for the Ultimate core. A Repository should implement the declared methods. Different
 * implementations can be used in order to try different technologies like persisting as object serialization, storing
 * in a database or using XML format.
 * 
 * Repository access should be implemented against this interface in order to abstract from the used persistence
 * technology.
 * 
 * @author Björn Buchhold
 * 
 */
public interface IRepository<K, T> {

	/**
	 * 
	 * Stores an Instance, including all references in the repository using the provided key. The instance should be
	 * available in the repository through the key, afterwards. This method strictly forbids overwriting existing
	 * objects in the repository
	 * 
	 * @param key
	 *            The key for the repository entry. It should uniquely identify the stored object
	 * @param transientInstance
	 *            The instance to be stored in the repository.
	 * @throws StoreObjectException
	 *             if the object can not be stored this exception is thrown
	 */
	void add(K key, T transientInstance) throws DuplicateKeyException, StoreObjectException;

	/**
	 * Stores an Instance, including all references in the repository using the provided key. The instance should be
	 * available in the repository through the key, afterwards. This method strictly allows overwriting existing objects
	 * in the repository
	 * 
	 * @param key
	 *            The key for the repository entry. It should uniquely identify the stored object
	 * @param transientInstance
	 *            The instance to be stored in the repository.
	 * @throws StoreObjectException
	 *             if the object can not be stored this exception is thrown
	 */
	void addOrReplace(K key, T transientInstance) throws StoreObjectException;

	/**
	 * method for retrieval of a stored object. Gets the objects corresponding to the provided key if it exists.
	 * Otherwise an Exception is throw.
	 * 
	 * @param key
	 *            key of the object to be gotten form the repository
	 * @return object referenced by the provided key
	 * @throws PersistentObjectNotFoundException
	 *             if the object does not exists, this exception should be thrown
	 * @throws PersistentObjectTypeMismatchException
	 *             if a class describing a type used in the stored object is not found, this exception is thrown
	 */
	T get(K key) throws PersistentObjectNotFoundException, PersistentObjectTypeMismatchException;

	/**
	 * removes the object stored under the provided key. does nothing if the key is not used
	 * 
	 * @param key
	 *            the key identifying the object to remove from the repository
	 * @return boolean indicating if something was in fact deleted
	 */
	boolean remove(K key);

	/**
	 * lists all keys of objects currently stored in the repository
	 * 
	 * @return a list of all keys referencing stored objects
	 */
	List<K> listKeys();

	/**
	 * removes objects from the repository that are referenced by the keys in the provided list
	 * 
	 * @param keys
	 *            list of the keys of the objects to remove from the repository
	 */
	void removeAll(List<K> keys);

	/**
	 * clears the complete repository. the repository should be empty after invoking this method
	 */
	void dump();

	/**
	 * checks if the repository is empty
	 * 
	 * @return true if the repository is empty, false if it contains something
	 */
	boolean isEmpty();
}
