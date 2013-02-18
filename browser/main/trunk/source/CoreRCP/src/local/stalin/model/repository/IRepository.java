/*
 * Project:	CoreRCP
 * Package:	local.stalin.model.repository
 * File:	IRepository.java created on Oct 28, 2009 by Björn Buchhold 
 *
 */
package local.stalin.model.repository;

import java.util.List;

/**
 * Repository interface for the STALIN core. A Repository should implement the
 * declared methods. Different implementations can be used in order to try
 * different technologies like persisting as object serialization, storing in a
 * database or using XML format.
 * 
 * Repository access should be implemented against this interface in order to
 * abstract from the used persistence technology.
 * 
 * @author Björn Buchhold
 * 
 */
public interface IRepository<K, T> {

	/**
	 * 
	 * Stores an Instance, including all references in the repository using the
	 * provided key. The instance should be available in the repository through
	 * the key, afterwards. This method strictly forbids overwriting existing
	 * objects in the repository
	 * 
	 * @param key
	 *            The key for the repository entry. It should uniquely identify
	 *            the stored object
	 * @param transientInstance
	 *            The instance to be stored in the repository.
	 * @throws StoreObjectException
	 *             if the object can not be stored this exception is thrown
	 */
	public void add(K key, T transientInstance) throws DuplicateKeyException,
			StoreObjectException;

	/**
	 * Stores an Instance, including all references in the repository using the
	 * provided key. The instance should be available in the repository through
	 * the key, afterwards. This method strictly allows overwriting existing
	 * objects in the repository
	 * 
	 * @param key
	 *            The key for the repository entry. It should uniquely identify
	 *            the stored object
	 * @param transientInstance
	 *            The instance to be stored in the repository.
	 * @throws StoreObjectException
	 *             if the object can not be stored this exception is thrown
	 */
	public void addOrReplace(K key, T transientInstance)
			throws StoreObjectException;

	/**
	 * method for retrieval of a stored object. Gets the objects corresponding
	 * to the provided key if it exists. Otherwise an Exception is throw.
	 * 
	 * @param key
	 *            key of the object to be gotten form the repository
	 * @return object referenced by the provided key
	 * @throws PersistentObjectNotFoundException
	 *             if the object does not exists, this exception should be
	 *             thrown
	 * @throws PersistentObjectTypeMismatchException
	 *             if a class describing a type used in the stored object is not
	 *             found, this exception is thrown
	 */
	public T get(K key) throws PersistentObjectNotFoundException,
			PersistentObjectTypeMismatchException;

	/**
	 * removes the object stored under the provided key. does nothing if the key
	 * is not used
	 * 
	 * @param key
	 *            the key identifying the object to remove from the repository
	 * @return boolean indicating if something was in fact deleted
	 */
	public boolean remove(K key);

	/**
	 *lists all keys of objects currently stored in the repository
	 * 
	 * @return a list of all keys referencing stored objects
	 */
	public List<K> listKeys();

	/**
	 * removes objects from the repository that are referenced by the keys in
	 * the provided list
	 * 
	 * @param keys
	 *            list of the keys of the objects to remove from the repository
	 */
	public void removeAll(List<K> keys);

	/**
	 * clears the complete repository. the repository should be empty after
	 * invoking this method
	 */
	public void dump();

	/**
	 * checks if the repository is empty
	 * 
	 * @return true if the repository is empty, false if it contains something
	 */
	public boolean isEmpty();
}
