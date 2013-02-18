/*
 * Project:	CoreRCP
 * Package:	local.stalin.model.repository
 * File:	SerializationRepository.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package local.stalin.model.repository;

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

import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;
import local.stalin.model.ModelContainer;

import org.apache.log4j.Logger;

/**
 * SerializationRepository
 *
 * @author Björn Buchhold
 *
 */
public class SerializationRepository implements IRepository<String, ModelContainer> {
	
	private File fileSystemDirectory;
	private static Logger s_logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Constructor for {@link SerializationRepository}.
	 * Constructs a repository that uses {@link Serializable} to persist objects
	 * in the file system .
	 * 
	 * @param fileSystemDirectory the directory in the local file system used by the repository to 
	 * store the files containing the persisted objects
	 */
	public SerializationRepository(File fileSystemDirectory){
		this.fileSystemDirectory=fileSystemDirectory;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#dump()
	 */
	@Override
	public void dump() {
		this.removeAll(this.listKeys());
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#get(java.lang.Object)
	 */
	@Override
	public ModelContainer get(String key)
			throws PersistentObjectNotFoundException, PersistentObjectTypeMismatchException {
		if(this.listKeys().contains(key)){
			try {
				s_logger.debug("deserializing model");
				Object obj = deserialize(key);
				return (ModelContainer) obj;
			} catch (FileNotFoundException e) {
				throw new PersistentObjectNotFoundException(e);
			} catch (IOException e) {
				throw new PersistentObjectNotFoundException(e);
			} catch (ClassNotFoundException e) {
				throw new PersistentObjectTypeMismatchException("A required class used" +
						" in the stored object graph could not be found. Maybe it has been produced by a plug-in that didn't export this package", e);
			}
		}else{
			throw new PersistentObjectNotFoundException("No object found using the key: " + key);
		}
	}

	/**
	 * ModelContainer deserialize
	 * @param key Model key.
	 * @return Deserialized model.
	 * @throws ClassNotFoundException 
	 * @throws IOException 
	 * @throws FileNotFoundException 
	 */
	private Object deserialize(String key) throws FileNotFoundException, IOException, ClassNotFoundException {
		return new ObjectInputStream(new FileInputStream(keyToFile(key))).readObject();
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#listKeys()
	 */
	@Override
	public List<String> listKeys() {
		//initialize return value 
		List<String> keys = new LinkedList<String>();
		for (String fileName : this.fileSystemDirectory.list()) {
			File file = new File(fileName);
			if (file.getName().endsWith(".ser")){
				//only keep the name. Throw away path and extension
				keys.add(file.getName().substring(0, file.getName().length()-4));
			}
		}
		return keys;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#remove(java.lang.Object)
	 */
	@Override
	public boolean remove(String key) {
		File toBeDeleted = new File(this.fileSystemDirectory+"/"+key+".ser");
		boolean success = toBeDeleted.delete();
		if(!success && this.listKeys().contains(key)){
			s_logger.warn("Could not delete " + toBeDeleted.getPath() + " from the file system!");
			return false;
		}else{
		 	s_logger.debug("Now, the model is not in the repository (anymore)");
		 	return true;
		}
		
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#removeAll(java.util.List)
	 */
	@Override
	public void removeAll(List<String> keys) {
		for (String string : keys) {
			this.remove(string);
		}
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#add(java.lang.Object, java.lang.Object)
	 */
	@Override
	public void add(String key, ModelContainer transientInstance)
			throws DuplicateKeyException, StoreObjectException {
		if(this.listKeys().contains(key)){
			throw new DuplicateKeyException("The key: " + key + " is already in use. If you want to " +
					"replace the stored object, use method addOrReplace instead!");
		}else{
			this.addOrReplace(key, transientInstance);
		}
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#addOrReplace(java.lang.Object, java.lang.Object)
	 */
	@Override
	public void addOrReplace(String key, ModelContainer transientInstance) throws StoreObjectException {
		try {
			serializie(key, transientInstance);
		} catch (FileNotFoundException e) {
			throw new InvalidKeyException("invalid key: " + key, e);
		} catch (IOException e) {
			throw new StoreObjectException(e);
		}		
	}

	/**
	 * void serializie
	 * @param key
	 * @param transientInstance
	 * @throws IOException 
	 * @throws FileNotFoundException 
	 */
	private void serializie(String key, ModelContainer transientInstance) throws FileNotFoundException, IOException {
		new ObjectOutputStream(new FileOutputStream(keyToFile(key))).writeObject(transientInstance);
		s_logger.debug("serialized model");
	}

	/**
	 * String keyToFile
	 * @param key Key to convert.
	 * @return File to store model represented by key.
	 */
	private File keyToFile(String key) {
		return new File(this.fileSystemDirectory+"/"+key+".ser");
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.repository.IRepository#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return listKeys().size()==0;
	}

}
