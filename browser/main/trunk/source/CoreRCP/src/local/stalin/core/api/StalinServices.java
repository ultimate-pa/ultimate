/*
 * Project:	CoreRCP
 * Package:	local.stalin.api
 * File:	StalinAPI.java created on Nov 19, 2009 by Björn Buchhold
 *
 */
package local.stalin.core.api;

import java.util.List;

import local.stalin.core.coreplugin.Application;
import local.stalin.core.coreplugin.Application.Stalin_Mode;
import local.stalin.core.coreplugin.preferences.IPreferenceConstants;
import local.stalin.core.coreplugin.preferences.LoggingDetailsPreferencePage;
import local.stalin.core.coreplugin.preferences.LoggingPreferencePage;
import local.stalin.core.coreplugin.preferences.LoggingToolsPreferencePage;
import local.stalin.core.coreplugin.toolchain.IStorable;
import local.stalin.ep.interfaces.ITool;
import local.stalin.logging.StalinLoggerFactory;
import local.stalin.model.GraphNotFoundException;
import local.stalin.model.GraphType;
import local.stalin.model.IModelManager;
import local.stalin.model.IPayload;
import local.stalin.model.StalinUID;
import local.stalin.model.repository.IRepository;
import local.stalin.model.repository.StoreObjectException;

import org.apache.log4j.Logger;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;

/**
 * StalinServices
 * 
 * STALIN API and designated point for other plug-ins to access core
 * functionality. Uses a singleton with public instance methods.<br/>
 * <br/>
 * 
 * Usage: Plug-ins obtain a singleton instance via the static getter
 * {@link StalinServices#getInstance()}. The instance is created and maintained
 * by {@link Application} and has knowledge of all necessary internal states.
 * 
 * 
 * @since 2.0
 * @author Björn Buchhold, Christian Simon
 * 
 */
public class StalinServices {

	/**
	 * private constructor to make this a singleton
	 * 
	 * @param modelManager
	 *            the current {@link IModelManager}
	 * @param application
	 *            the current instance of {@link Application}
	 */
	private StalinServices(IModelManager modelManager, Application application) {
		this.m_Application = application;
		this.m_ModelManager = modelManager;
	}

	/**
	 * StalinServices instance the singleton instance
	 */
	private static StalinServices s_Instance;

	/**
	 * Members. they keep information on the current state of the core
	 */

	private IModelManager m_ModelManager;
	private Application m_Application;

	/**
	 * Getter for the singleton instance. Plug-ins should always call this
	 * method to obtain a instance of StalinServices. The core takes care that
	 * this instance is up to date.<br/>
	 * <br/>
	 * 
	 * All further functionality is provided as public instance methods by the
	 * returned instance.
	 * 
	 * @return the singleton instance of StalinServices
	 */
	public static StalinServices getInstance() {
		return s_Instance;
	}

	/**
	 * Creates the singleton instance. Should only be called by
	 * {@link Application}
	 * 
	 * @param application
	 *            the current instance of {@link Application}
	 */
	public static void createInstance(Application application) {
		s_Instance = new StalinServices(null, application);
	}

	/**
	 * Sets the current ModelManager. Should only be called by
	 * {@link Application}
	 * 
	 * @param modelManager
	 *            the current instance of {@link IModelManager}
	 */
	public void setModelManager(IModelManager modelManager) {
		this.m_ModelManager = modelManager;
	}

	/**
	 * Method to obtain models that are currently kept in memory List<GraphType>
	 * getModelsInMemory
	 * 
	 * @see IModelManager#getItemKeys()
	 * @return Graph>Types of all models in the memory
	 */
	public List<GraphType> getModelsInMemory() {
		return this.m_ModelManager.getItemKeys();
	}

	/**
	 * Gets a GraphType object <=> model id by its String representation
	 * 
	 * @see IModelManager#getGraphTypeById(String)
	 * @param modelId
	 *            the String representation of the GraphType
	 * @return the corresponding GraphType object
	 */
	public GraphType getGraphTypeFromStringModelId(String modelId) {
		return this.m_ModelManager.getGraphTypeById(modelId);
	}

	/**
	 * Gets a GraphType object <=> model id by its Creator Plug-in ID
	 * 
	 * @see IModelManager#getGraphTypeByGeneratorPluginId(String)
	 * @param pluginId
	 *            the plug-in of the creator of the GraphType
	 * @return the corresponding GraphType object
	 */
	public GraphType getGraphTypeByCreatorPluginId(String pluginId) {
		return this.m_ModelManager.getGraphTypeByGeneratorPluginId(pluginId);
	}

	/**
	 * Obtains all models. This includes models that are currently in the memory
	 * as well as perrsisent models in the repository
	 * 
	 * @return the String identifier of all models in memory and repository
	 */
	public List<String> getAllModels() {
		return this.m_ModelManager.getItemNames();
	}

	/**
	 * Removes a model from the memory to free resources.
	 * 
	 * @param graphType
	 *            id of the model
	 * @return flag indicating success
	 */
	public boolean removeModelFromMemory(GraphType graphType) {
		return this.m_ModelManager.removeItem(graphType);
	}

	/**
	 * Searches for a payload an element of the specified model.
	 * 
	 * @see IModelManager#search(GraphType, StalinUID)
	 * @param modelId
	 *            the identifier of the model to be searched in
	 * @param id
	 *            the identifier of the element to be search for in the model
	 * @return Payload of the specified graph.
	 */
	public IPayload search(GraphType modelId, StalinUID id) {
		return this.m_ModelManager.search(modelId, id);
	}

	/**
	 * Searches for a payload an element of the specified model.
	 * 
	 * @see IModelManager#search(GraphType, StalinUID)
	 * @param modelId
	 *            the identifier of the model to be searched in
	 * @param id
	 *            the identifier of the element to be search for in the model
	 * @return Payload of the specified graph.
	 */
	public IPayload search(GraphType modelId, String id) {
		return this.m_ModelManager.search(modelId, id);
	}

	/**
	 * Persists the existing graph in the {@link IModelManager}'s
	 * {@link IRepository}
	 * 
	 * @see IModelManager#persistExistingGraph(GraphType, boolean)
	 * @param graph
	 *            id of the model / graph to be persisted
	 * @param keepInMemory
	 *            flag that determines if the model is kept in memory in
	 *            addition to the created persistent instance
	 * @throws StoreObjectException
	 *             if creating the persistent object failed
	 * @throws GraphNotFoundException
	 *             if there is no model with the specified model id in the
	 *             {@link IModelManager}
	 * 
	 */
	public void persistExistingGraph(GraphType graph, boolean keepInMemory)
			throws StoreObjectException, GraphNotFoundException {
		this.m_ModelManager.persistExistingGraph(graph, keepInMemory);
	}

	/**
	 * Persists the existing graph in the {@link IModelManager}'s
	 * {@link IRepository}. Does not keep the model in memory
	 * 
	 * @see StalinServices#persistExistingGraph(GraphType, boolean)
	 * @see IModelManager#persistAndDropExistingGraph(GraphType)
	 * @param graph
	 *            id of the model / graph to be persisted
	 * @throws StoreObjectException
	 *             if creating the persistent object failed
	 * @throws GraphNotFoundException
	 *             if there is no model with the specified model id in the
	 *             {@link IModelManager}
	 */
	public void persistExistingGraph(GraphType graph)
			throws StoreObjectException, GraphNotFoundException {
		this.m_ModelManager.persistAndDropExistingGraph(graph);
	}

	/**
	 * Gets the correct logger for an asking plug-in This method should be
	 * called by all plug-ins that extend {@link ITool} and by the Core Plugin
	 * and want to access their {@link Logger}. Appenders are set as defaults
	 * and log levels are set using Eclipse {@link IPreferenceStore} and the
	 * {@link PreferencePage}s: {@link LoggingDetailsPreferencePage} and
	 * {@link LoggingPreferencePage} <br/>
	 * <br/>
	 * <b>Usage:</b> Most tools can use their Activator.s_PLUGIN_ID as argument<br/>
	 * <br/>
	 * Not to be used for external tools or the controller plug-in
	 * 
	 * @param pluginId
	 *            The PluginId of the plug-in that asks for its {@link Logger}
	 * @return the log4j {@link Logger} for the plug-in
	 */
	public Logger getLogger(String pluginId) {
		return StalinLoggerFactory.getInstance().getLoggerById(pluginId);
	}

	/**
	 * Gets the correct logger for an asking external tool This method should be
	 * called by all external tools that want to access their {@link Logger}.
	 * Appenders are set as defaults and log levels are set using the Eclipse
	 * {@link IPreferenceStore} and the {@link PreferencePage}s:
	 * {@link LoggingToolsPreferencePage} and {@link LoggingPreferencePage} <br/>
	 * <br/>
	 * 
	 * Not to be used for plug-ins!
	 * 
	 * @param id
	 *            An identifier for the external tool that asks for its
	 *            {@link Logger}
	 * @return the log4j {@link Logger} for the external tool
	 */
	public Logger getLoggerForExternalTool(String id) {
		return StalinLoggerFactory.getInstance().getLoggerById(
				IPreferenceConstants.EXTERNAL_TOOLS_PREFIX + id);
	}

	/**
	 * Gets the correct logger for the controller plug-in. This method should be
	 * called by all controller plug-ins that want to access their
	 * {@link Logger}. Appenders are set as defaults and log levels are set
	 * using the Eclipse {@link IPreferenceStore} and the {@link PreferencePage}
	 * : {@link LoggingPreferencePage} <br/>
	 * <br/>
	 * 
	 * @return Logger for the current controller.
	 */
	public Logger getControllerLogger() {
		return StalinLoggerFactory.getInstance().getLoggerById(
				StalinLoggerFactory.LOGGER_NAME_CONTROLLER);
	}

	/**
	 * Gets the Plug-In ID of the controller that is currently active.
	 * 
	 * @return The ID of the Controller Plug-In or null if none is present at
	 *         that point in time
	 */
	public String getActiveControllerId() {
		return this.m_Application.getActiveControllerId();
	}

	/**
	 * Accessor for objects that are stored during tool-chain execution
	 * 
	 * @param key
	 *            the key of the stored object
	 * @return the stored instance if {@link IStorable}
	 */
	public IStorable getStoredObject(String key) {
		return this.m_Application.getStoredToolchainUse().getStoredObject(key);
	}

	/**
	 * allows storing an {@link IStorable} in the current tool-chain's store.
	 * 
	 * @param key
	 *            key of the stored object
	 * @param value
	 *            the instance of {@link IStorable} to be stored
	 */
	public void putInToolchainStore(String key, IStorable value) {
		this.m_Application.getStoredToolchainUse().putIntoStorage(key, value);
	}

	/**
	 * Finds out which plug-ins are loaded
	 * 
	 * @return a list of all active tools
	 */
	public List<ITool> getActiveTools() {
		return this.m_Application.getAllTools();
	}

	/**
	 * Provides information on the question if stalin is in GUI or some other
	 * mode.
	 * 
	 * @return the current mode that is set
	 */
	public Stalin_Mode getStalinMode() {
		return this.m_Application.getCoreMode();
	}

	/**
	 * removes a model from the model manager. also removes persistent models
	 * 
	 * @param id
	 *            GraphType identifying the model.
	 * @return true if the model was removed successfully, false otherwise
	 */
	public boolean removeModel(GraphType id) {
		return this.m_ModelManager.removeItem(id);
	}

	/**
	 * removes a model from the model manager. also removes persistent models
	 * 
	 * @param id
	 *            String representation of the GraphType identifying the model.
	 * @return true if the model was removed successfully, false otherwise
	 */
	public boolean removeModel(String id) {
		return this.m_ModelManager.removeItem(id);
	}
}
