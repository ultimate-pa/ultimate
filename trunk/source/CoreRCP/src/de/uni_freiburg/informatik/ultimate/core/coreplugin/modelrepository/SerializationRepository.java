/*
 * Copyright (C) 2009-2015 Björn Buchhold
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
 * File:	SerializationRepository.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.modelrepository;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.ModelContainer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.DuplicateKeyException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.InvalidKeyException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.PersistentObjectNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.PersistentObjectTypeMismatchException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * SerializationRepository
 * 
 * @author Björn Buchhold
 * 
 */
public class SerializationRepository implements IRepository<String, ModelContainer> {

	private final File mFileSystemDirectory;
	private final ILogger mLogger;

	/**
	 * Constructor for {@link SerializationRepository}. Constructs a repository
	 * that uses {@link Serializable} to persist objects in the file system .
	 * 
	 * @param fileSystemDirectory
	 *            the directory in the local file system used by the repository
	 *            to store the files containing the persisted objects
	 */
	public SerializationRepository(File fileSystemDirectory, ILogger logger) {
		assert logger != null;
		mFileSystemDirectory = fileSystemDirectory;
		mLogger = logger;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#dump()
	 */
	@Override
	public void dump() {
		removeAll(listKeys());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#get(
	 * java.lang.Object)
	 */
	@Override
	public ModelContainer get(String key) throws PersistentObjectNotFoundException,
			PersistentObjectTypeMismatchException {
		if (listKeys().contains(key)) {
			try {
				mLogger.debug("deserializing model");
				final Object obj = deserialize(key);
				return (ModelContainer) obj;
			} catch (final FileNotFoundException e) {
				throw new PersistentObjectNotFoundException(e);
			} catch (final IOException e) {
				throw new PersistentObjectNotFoundException(e);
			} catch (final ClassNotFoundException e) {
				throw new PersistentObjectTypeMismatchException(
						"A required class used"
								+ " in the stored object graph could not be found. Maybe it has been produced by a plug-in that didn't export this package",
						e);
			}
		} else {
			throw new PersistentObjectNotFoundException("No object found using the key: " + key);
		}
	}

	/**
	 * ModelContainer deserialize
	 * 
	 * @param key
	 *            Model key.
	 * @return Deserialized model.
	 * @throws ClassNotFoundException
	 * @throws IOException
	 * @throws FileNotFoundException
	 */
	private Object deserialize(String key) throws FileNotFoundException, IOException, ClassNotFoundException {

		final ObjectInputStream stream = new ObjectInputStream(new FileInputStream(keyToFile(key)));
		final Object rtr = stream.readObject();
		stream.close();
		return rtr;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#listKeys
	 * ()
	 */
	@Override
	public List<String> listKeys() {
		// initialize return value
		final List<String> keys = new LinkedList<String>();
		for (final String fileName : mFileSystemDirectory.list()) {
			final File file = new File(fileName);
			if (file.getName().endsWith(".ser")) {
				// only keep the name. Throw away path and extension
				keys.add(file.getName().substring(0, file.getName().length() - 4));
			}
		}
		return keys;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#remove
	 * (java.lang.Object)
	 */
	@Override
	public boolean remove(String key) {
		final File toBeDeleted = new File(mFileSystemDirectory + "/" + key + ".ser");
		final boolean success = toBeDeleted.delete();
		if (!success && listKeys().contains(key)) {
			mLogger.warn("Could not delete " + toBeDeleted.getPath() + " from the file system!");
			return false;
		} else {
			mLogger.debug("Now, the model is not in the repository (anymore)");
			return true;
		}

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#removeAll
	 * (java.util.List)
	 */
	@Override
	public void removeAll(List<String> keys) {
		for (final String string : keys) {
			remove(string);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#add(
	 * java.lang.Object, java.lang.Object)
	 */
	@Override
	public void add(String key, ModelContainer transientInstance) throws DuplicateKeyException, StoreObjectException {
		if (listKeys().contains(key)) {
			throw new DuplicateKeyException("The key: " + key + " is already in use. If you want to "
					+ "replace the stored object, use method addOrReplace instead!");
		} else {
			addOrReplace(key, transientInstance);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#addOrReplace
	 * (java.lang.Object, java.lang.Object)
	 */
	@Override
	public void addOrReplace(String key, ModelContainer transientInstance) throws StoreObjectException {
		try {
			serializie(key, transientInstance);
		} catch (final FileNotFoundException e) {
			throw new InvalidKeyException("invalid key: " + key, e);
		} catch (final IOException e) {
			mLogger.fatal("Serialization of ModelContainer failed for key " + key + " to file " + keyToFile(key));
			throw new StoreObjectException(e);
		}
	}

	/**
	 * void serializie
	 * 
	 * @param key
	 * @param transientInstance
	 * @throws IOException
	 * @throws FileNotFoundException
	 */
	private void serializie(String key, ModelContainer transientInstance) throws FileNotFoundException, IOException {
		final ObjectOutputStream stream = new ObjectOutputStream(new FileOutputStream(keyToFile(key)));
		stream.writeObject(transientInstance);
		stream.close();
		mLogger.debug("serialized model");
	}

	/**
	 * String keyToFile
	 * 
	 * @param key
	 *            Key to convert.
	 * @return File to store model represented by key.
	 */
	private File keyToFile(String key) {
		return new File(mFileSystemDirectory + File.separator + sanitize(key) + ".ser");
	}

	/**
	 * Should replace all illegal characters in a filename with '_' . It is not
	 * sure if it catches all invalid filenames on all OS.
	 * 
	 * @param filename
	 *            - A string that will be used as a filename (paths will not
	 *            work!) somewhere else.
	 * @return A string having converted all illegal characters in filename to
	 *         '_'
	 */
	private String sanitize(String filename) {
		return filename.replaceAll("[\\/:\"*?<>|]+", "_");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.repository.IRepository#isEmpty
	 * ()
	 */
	@Override
	public boolean isEmpty() {
		return listKeys().size() == 0;
	}

}
