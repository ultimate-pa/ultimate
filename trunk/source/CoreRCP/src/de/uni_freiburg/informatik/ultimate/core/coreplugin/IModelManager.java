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
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	IModelManager.java created on Nov 11, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;

/**
 * IModelManager
 * 
 * The new model manager has access to a repository where models can be put. At
 * any time a model can still be kept in the memory using the map. Additionally
 * it can be persisted in the repository.
 * 
 * Models can be removed from the model manager as before but if the model
 * manager is queries for it and does not find it in the vault map, it looks in
 * the repository.
 * 
 * 
 * @author Björn Buchhold
 * 
 */
public interface IModelManager {

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
	boolean addItem(IElement rootNode, ModelType graphtype);

	/**
	 * Should remove whole tree/graph independent of node position in this tree
	 * or prune tree/graph at this position (for graphs possibly removing the
	 * whole graph). Also removes persistent instances
	 * 
	 * @param graphtype
	 *            the graph to remove
	 * @return true if the graphtype has been removed, false otherwise
	 */
	boolean removeItem(ModelType graphtype);

	/**
	 * Should remove whole tree/graph independent of node position in this tree
	 * or prune tree/graph at this position (for graphs possibly removing the
	 * whole graph). Also removes persistent instances
	 * 
	 * @param id
	 *            the string representation of the graph to remove
	 * @return true if the model has been removed, false otherwise
	 */
	boolean removeItem(String id);

	/**
	 * persist an existing graph. Does not keep the Graph in memory!
	 * 
	 * @param key
	 *            id of the model as graphtype
	 * @throws StoreObjectException
	 * @throws GraphNotFoundException
	 */
	void persistAndDropExistingGraph(ModelType key)
			throws StoreObjectException, GraphNotFoundException;

	/**
	 * persist an existing graph. May choose if the graph is kept or removed
	 * from the memory
	 * 
	 * @param key
	 *            id of the model as graphtype
	 * @param keepInMemory
	 *            boolean indicating of the model should also be kept in memory
	 * @throws StoreObjectException
	 * @throws GraphNotFoundException
	 */
	void persistExistingGraph(ModelType key, boolean keepInMemory)
			throws StoreObjectException, GraphNotFoundException;

	/**
	 * persists all models. May choose if the models are kept or removed from
	 * the memory
	 * 
	 * @param keepInMemory
	 *            boolean indicating of the model should also be kept in memory
	 * @throws StoreObjectException
	 */
	void persistAll(boolean keepInMemory) throws StoreObjectException;

	/**
	 * Removes an existing object from the Chamber
	 * 
	 * @param vault
	 * @return false if vault is not present in chamber - method does not remove
	 *         the vault in this case; true otherwise
	 */
	boolean removeItem(ModelContainer vault);

	/**
	 * Checks if the model manager is empty. works regarding the memory model,
	 * not the persistent repository
	 * 
	 * @return true if it's empty, false if there is at least one model present
	 */
	boolean isEmpty();

	/**
	 * Gives the size of the memory map, not the repository
	 * 
	 * @return the size of the in-memory hash map
	 */
	int size();

	/**
	 * removes all models from the model manager. Only in-memory model are
	 * affected and not persisted models.
	 */
	void removeAll();


	/**
	 * 
	 * @return A list of the names of all models that are accessible. Includes
	 *         models in the repository
	 */
	ArrayList<String> getItemNames();

	/**
	 * Get the GraphType object for its String representation
	 * 
	 * @param s
	 *            the String representation of the desired GraphType
	 * @return the corresponding GraphType object
	 */
	ModelType getGraphTypeById(String s);

	/**
	 * Get the GraphType object that identifies a model generated by a certain
	 * plug-in
	 * 
	 * @param id
	 *            the plug-in id of the generator
	 * @return the model generated by the specified plug-in
	 */
	ModelType getGraphTypeByGeneratorPluginId(String id);

	/**
	 * INode getRootNode
	 * 
	 * @param graphType
	 * @return Root node of corresponding graph
	 * @throws GraphNotFoundException
	 */
	IElement getRootNode(ModelType graphType) throws GraphNotFoundException;

	/**
	 * void showStatus
	 * 
	 * @param callerName
	 */
	void showStatus(String callerName);

	/**
	 * void setLastAdded
	 * 
	 * @param lastAdded
	 *            the model that has been added recently
	 */
	void setLastAdded(ModelType lastAdded);

	/**
	 * GraphType getLastAdded
	 * 
	 * @return the model that has been added most recently.
	 */
	ModelType getLastAdded();

	/**
	 * List<GraphType> getItemKeys
	 * 
	 * Note: Does not return keys of items persisted in the repository
	 * 
	 * @return Graph types in the memory map of the memory manager
	 * 
	 */
	List<ModelType> getItemKeys();
}
