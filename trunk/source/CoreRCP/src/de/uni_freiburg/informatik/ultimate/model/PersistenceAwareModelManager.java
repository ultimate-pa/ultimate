/*
� * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	PersistenceAwareModelManager.java created on Nov 11, 2009 by Bj�rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.repository.DataAccessException;
import de.uni_freiburg.informatik.ultimate.model.repository.IRepository;
import de.uni_freiburg.informatik.ultimate.model.repository.PersistentObjectNotFoundException;
import de.uni_freiburg.informatik.ultimate.model.repository.PersistentObjectTypeMismatchException;
import de.uni_freiburg.informatik.ultimate.model.repository.SerializationRepository;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.plugins.Constants;

/**
 * PersistenceAwareModelManager
 * 
 * Standard implementation of the {@link IModelManager} A
 * {@link PersistenceAwareModelManager} is created using a repository. The
 * default repository is the System's java temporary directory. There should be
 * a property page to set the repository's location in the file system to a
 * desired value
 * 
 * The ModelManager should be used for any access to models produced by previous
 * tool runs.
 * 
 * The Application may ask the ModelManager to persist and models and probably
 * drop them from the in-memory map. Subsequent access to such a model is
 * dispatched to the repository and the model is added to the memory-map, again
 * 
 * @author Björn Buchhold
 * 
 */
public class PersistenceAwareModelManager implements IModelManager {

	private Map<GraphType, ModelContainer> mModelMap;
	private IRepository<String, ModelContainer> mRepository;
	private Logger mLogger;
	private GraphType mLastAdded;

	public PersistenceAwareModelManager(File repositoryRoot, Logger logger) {
		assert logger != null;
		mModelMap = new HashMap<GraphType, ModelContainer>();
		mLogger = logger;
		mLogger.info("Repository-Root is: " + repositoryRoot.getAbsolutePath());
		this.mRepository = new SerializationRepository(repositoryRoot, mLogger);
	}

	public PersistenceAwareModelManager(String tmp_dir, Logger logger) {
		this(new File(tmp_dir), logger);
	}

	/**
	 * String createFileNameFromNode
	 * 
	 * @param node
	 * @return File name for a given node.
	 */
	private String createFileNameFromNode(IElement node) {
		if (node == null) {
			return "";
		}
		String graphName = "";
		if (node.hasPayload()) {
			if (node.getPayload().hasLocation()) {
				graphName = node.getPayload().getLocation().getFileName();
			}
		}
		if (graphName.contains(Constants.getFileSep())) {
			String fileSep = Constants.getFileSep();
			String[] names = graphName.split(fileSep);
			graphName = "";
			for (String s : names) {
				graphName += s.substring(s.lastIndexOf(File.separator) + 1) + fileSep;
			}
			graphName = graphName.substring(0, graphName.length() - 2);
		} else {
			graphName = graphName.trim();
			graphName = graphName.substring(graphName.lastIndexOf(File.separator) + 1);
		}
		return graphName;
	}

	/**
	 * Adds a new vault to the Chamber
	 * 
	 * @param vault
	 * @return false if vault is present in chamber - method does not add the
	 *         vault in this case; true otherwise
	 */
	private boolean addItem(ModelContainer vault) {
		if (this.mModelMap.containsKey(vault.getType())) {
			mLogger.warn("Model is already present, skipping insertion....");
			return false;
		} else {
			this.mModelMap.put(vault.getType(), vault);
			mLogger.debug("Inserting " + vault);
			setLastAdded(vault.getType());
			return true;
		}
	}

	/**
	 * Adds a new (sub)graph or (sub)tree to the Chamber
	 * 
	 * @param rootNode
	 *            The node itself and all its children and so on are added as
	 *            own model to the chamber (in a cyclic graph possibly adding
	 *            the whole graph, especially the parents of this node)
	 * @param graphtype
	 *            The concrete type of graph this node belongs to (should this
	 *            be calculated or set somehow here ? )
	 * @return false if vault is present in chamber - method does not add the
	 *         vault in this case; true otherwise
	 */
	public boolean addItem(IElement rootNode, GraphType graphtype) {
		ModelContainer vault = new ModelContainer(rootNode, graphtype, createFileNameFromNode(rootNode));
		setLastAdded(vault.getType());
		return this.addItem(vault);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#getItemNames()
	 */
	@Override
	public ArrayList<String> getItemNames() {
		ArrayList<String> names = new ArrayList<String>();
		for (GraphType t : this.mModelMap.keySet()) {
			names.add(t.toString());
		}
		names.addAll(this.mRepository.listKeys());
		return names;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#getLastAdded()
	 */
	@Override
	public GraphType getLastAdded() {
		return this.mLastAdded;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#getRootNode(de
	 * .uni_freiburg.informatik.ultimate.model.GraphType )
	 */
	@Override
	public IElement getRootNode(GraphType graph) throws GraphNotFoundException {
		ModelContainer container = this.mModelMap.get(graph);
		if (container == null) {
			try {
				container = this.mRepository.get(graph.toString());
				this.mModelMap.put(graph, container);
			} catch (PersistentObjectNotFoundException e) {
				throw new GraphNotFoundException(graph, e);
			} catch (PersistentObjectTypeMismatchException e) {
				mLogger.error("Could not deserialize graph " + graph, e);
				throw new GraphNotFoundException(graph, e);
			}
		}
		return container.getRoot();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IModelManager#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return (this.mModelMap.isEmpty() && this.mRepository.isEmpty());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#persistAll(boolean
	 * )
	 */
	@Override
	public void persistAll(boolean keepInMemory) throws StoreObjectException {
		for (Entry<GraphType, ModelContainer> mapEntry : this.mModelMap.entrySet()) {
			this.mRepository.addOrReplace(mapEntry.getKey().toString(), mapEntry.getValue());
		}
		if (!keepInMemory) {
			this.removeAll();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#persistExistingGraph
	 * (de.uni_freiburg.informatik.ultimate.model .GraphType)
	 */
	@Override
	public void persistAndDropExistingGraph(GraphType key) throws StoreObjectException, GraphNotFoundException {
		persistExistingGraph(key, false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#persistExistingGraph
	 * (de.uni_freiburg.informatik.ultimate.model .GraphType, boolean)
	 */
	@Override
	public void persistExistingGraph(GraphType key, boolean keepInMemory) throws StoreObjectException,
			GraphNotFoundException {
		if (this.mModelMap.containsKey(key)) {
			this.mRepository.addOrReplace(key.toString(), this.mModelMap.get(key));
			if (!keepInMemory) {
				this.mModelMap.remove(key);
			}
		} else {
			throw new GraphNotFoundException(key);
		}

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IModelManager#removeAll()
	 */
	@Override
	public void removeAll() {
		this.mModelMap.clear();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#removeItem(de
	 * .uni_freiburg.informatik.ultimate.model.GraphType)
	 */
	@Override
	public boolean removeItem(GraphType graphtype) {
		boolean successfull = true;
		if (this.mModelMap.containsKey(graphtype)) {
			successfull = this.mModelMap.remove(graphtype) != null;
		}
		return successfull && this.mRepository.remove(graphtype.toString());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#removeItem(java
	 * .lang.String)
	 */
	@Override
	public boolean removeItem(String id) {
		boolean successfull = true;
		GraphType graphType = getInMemoryGraphTypeById(id);
		if (graphType != null) {
			successfull = this.mModelMap.remove(graphType) != null;
		}
		return successfull && this.mRepository.remove(id);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#removeItem(de
	 * .uni_freiburg.informatik.ultimate.model.ModelContainer )
	 */
	@Override
	public boolean removeItem(ModelContainer vault) {
		return this.mModelMap.remove(vault.getType()) != null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#searchGraphType
	 * (java.lang.String)
	 */
	@Override
	public GraphType getGraphTypeById(String s) {
		for (GraphType t : this.mModelMap.keySet()) {
			if (t.toString().equals(s)) {
				return t;
			}
		}
		if (this.mRepository.listKeys().contains(s)) {
			try {
				return this.mRepository.get(s).getType();
			} catch (DataAccessException e) {
				mLogger.error("Problems deserializing persistent model: ", e);
			}
		}
		return null;
	}

	private GraphType getInMemoryGraphTypeById(String id) {
		for (GraphType t : this.mModelMap.keySet()) {
			if (t.toString().equals(id)) {
				return t;
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IModelManager#
	 * getGraphTypeByGeneratorPluginId(java .lang.String)
	 */
	@Override
	public GraphType getGraphTypeByGeneratorPluginId(String id) {
		for (GraphType t : this.mModelMap.keySet()) {
			if (t.getCreator().equals(id)) {
				return t;
			}
		}
		for (String keyFromRepos : this.mRepository.listKeys()) {
			if (keyFromRepos.contains(id)) {
				try {
					GraphType graphType = this.mRepository.get(keyFromRepos).getType();
					if (graphType.getCreator().equals(id))
						return graphType;
				} catch (DataAccessException e) {
					mLogger.error("Problems deserializing persistent model: ", e);
				}
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#setLastAdded(
	 * de.uni_freiburg.informatik.ultimate.model.GraphType )
	 */
	@Override
	public void setLastAdded(GraphType lastAdded) {
		this.mLastAdded = lastAdded;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#showStatus(java
	 * .lang.String)
	 */
	@Override
	public void showStatus(String callerName) {
		mLogger.debug(callerName + " reguests chamber status");
		int i = 0;
		for (ModelContainer v : this.mModelMap.values()) {
			mLogger.debug("(" + i + ") " + "Name/Type/Size: " + v.getName() + " / " + v.getType() + " / " + v.getSize());
			i++;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IModelManager#size()
	 */
	@Override
	public int size() {
		mLogger.debug("Current MM size is " + mModelMap.size() + ". There are " + this.mRepository.listKeys().size()
				+ " models in the repository.");
		return this.mModelMap.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IModelManager#getItemKeys()
	 */
	@Override
	public List<GraphType> getItemKeys() {
		return new ArrayList<GraphType>(mModelMap.keySet());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IModelManager#search(de.
	 * uni_freiburg.informatik.ultimate.model.GraphType, java.lang.String)
	 */
	@Override
	public IPayload search(GraphType modelId, String id) {
		if (this.mModelMap.containsKey(modelId)) {
			return this.mModelMap.get(modelId).findNode(id);
		} else {
			try {
				ModelContainer container = this.mRepository.get(modelId.toString());
				this.mModelMap.put(modelId, container);
				return container.findNode(id);
			} catch (DataAccessException e) {
				mLogger.debug("Could not find requested GraphType in VaultMap.");
				return null;
			}
		}
	}

}
