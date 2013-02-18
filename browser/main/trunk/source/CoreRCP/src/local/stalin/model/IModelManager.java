/*
 * Project:	CoreRCP
 * Package:	local.stalin.model
 * File:	IModelManager.java created on Nov 11, 2009 by Björn Buchhold
 *
 */
package local.stalin.model;

import java.util.ArrayList;
import java.util.List;

import local.stalin.model.repository.StoreObjectException;

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
	boolean addItem(INode rootNode, GraphType graphtype);

	/**
	 * Should remove whole tree/graph independent of node position in this tree
	 * or prune tree/graph at this position (for graphs possibly removing the
	 * whole graph). Also removes persistent instances
	 * 
	 * @param graphtype
	 *            the graph to remove
	 * @return true if the graphtype has been removed, false otherwise
	 */
	boolean removeItem(GraphType graphtype);

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
	void persistAndDropExistingGraph(GraphType key)
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
	void persistExistingGraph(GraphType key, boolean keepInMemory)
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
	 * This method searches for a specific INode in a given (sub)graph via depth
	 * first search. If this node is present it will find it, else it returs
	 * NULL. Expects every parameter to be NOT NUll.
	 * 
	 * @param outerAnnotationKey
	 *            the String desciption of the outer annotation (e.g. the plugin
	 *            name that made this description)
	 * @param innerAnnotationKey
	 *            the String description of the inner annotation (e.g. the
	 *            keyword the specified plugin uses)
	 * @param innerAnnotationValue
	 *            the specific value at this point
	 * @param node
	 *            the root node of the subgraph
	 * @return null if no node was found, else the INode
	 * 
	 */
	INode search(String outerAnnotationKey, String innerAnnotationKey,
			Object innerAnnotationValue, INode node);

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
	GraphType getGraphTypeById(String s);

	/**
	 * Get the GraphType object that identifies a model generated by a certain
	 * plug-in
	 * 
	 * @param id
	 *            the plug-in id of the generator
	 * @return the model generated by the specified plug-in
	 */
	GraphType getGraphTypeByGeneratorPluginId(String id);

	/**
	 * INode getRootNode
	 * 
	 * @param graphType
	 * @return Root node of corresponding graph
	 * @throws GraphNotFoundException
	 */
	INode getRootNode(GraphType graphType) throws GraphNotFoundException;

	/**
	 * void showStatus
	 * 
	 * @param callerName
	 */
	void showStatus(String callerName);

	/**
	 * IPayload search
	 * 
	 * @param modelId
	 * @param id
	 * @return Payload of node with specified id in specified graph.
	 */
	IPayload search(GraphType modelId, StalinUID id);

	/**
	 * IPayload search for a payload of the requested element in the given model
	 * 
	 * @param modelId
	 *            GraphType identifying the model
	 * @param id
	 *            the id of the requested element
	 * @return the requested payload
	 */
	IPayload search(GraphType modelId, String id);

	/**
	 * IPayload search Searches for a payload of a certain element
	 * 
	 * @param rootNode
	 *            root node from which the search is started
	 * @param id
	 *            id of the requested element
	 * @return the requested payload
	 */
	IPayload search(INode rootNode, String id);

	/**
	 * void setLastAdded
	 * 
	 * @param lastAdded
	 *            the model that has been added recently
	 */
	void setLastAdded(GraphType lastAdded);

	/**
	 * GraphType getLastAdded
	 * 
	 * @return the model that has been added most recently.
	 */
	GraphType getLastAdded();

	/**
	 * List<GraphType> getItemKeys
	 * 
	 * Note: Does not return keys of items persisted in the repository
	 * 
	 * @return Graph types in the memory map of the memory manager
	 * 
	 */
	List<GraphType> getItemKeys();

}
