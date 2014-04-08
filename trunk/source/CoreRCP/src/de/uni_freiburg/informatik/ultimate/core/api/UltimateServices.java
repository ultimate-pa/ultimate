/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.api
 * File:	UltimateAPI.java created on Nov 19, 2009 by Bj�rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.api;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.IStorable;
import de.uni_freiburg.informatik.ultimate.core.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.logging.UltimateLoggerFactory;
import de.uni_freiburg.informatik.ultimate.model.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.UltimateUID;
import de.uni_freiburg.informatik.ultimate.model.repository.IRepository;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;

/**
 * UltimateServices
 * 
 * Ultimate API and designated point for other plug-ins to access core
 * functionality. Uses a singleton with public instance methods.<br/>
 * <br/>
 * 
 * Usage: Plug-ins obtain a singleton instance via the static getter
 * {@link UltimateServices#getInstance()}. The instance is created and
 * maintained by {@link UltimateCore} and has knowledge of all necessary
 * internal states.
 * 
 * 
 * @since 2.0
 * @author Bj�rn Buchhold, Christian Simon
 * 
 */
public class UltimateServices {

	/**
	 * private constructor to make this a singleton
	 * 
	 * @param modelManager
	 *            the current {@link IModelManager}
	 * @param application
	 *            the current instance of {@link UltimateCore}
	 */
	private UltimateServices(IModelManager modelManager, UltimateCore application) {
		this.m_Application = application;
		this.m_ModelManager = modelManager;
		this.m_ResultMap = new HashMap<String, List<IResult>>();
		mMonitoredProcesses = new ArrayList<MonitoredProcess>();
	}

	/**
	 * UltimateServices instance the singleton instance
	 */
	private static UltimateServices s_Instance;

	/**
	 * Members. they keep information on the current state of the core
	 */

	private IModelManager m_ModelManager;
	private UltimateCore m_Application;

	/**
	 * Here we store the found Results as a list. The key is the PluginID of the
	 * plugin
	 */
	private HashMap<String, List<IResult>> m_ResultMap;
	/**
	 * Mapping from Boogie identifier to C identifier.
	 */
	private Map<String, String> identifierMapping;

	/**
	 * Workaround. Needed until Daniels ModelContainer is ready.
	 */
	@Deprecated
	private List<ITranslator<?, ?, ?, ?>> m_TranslatorSequence;

	private List<MonitoredProcess> mMonitoredProcesses;

	public void registerProcess(MonitoredProcess mp) {
		synchronized (mMonitoredProcesses) {
			mMonitoredProcesses.add(mp);
		}
	}

	public void unregisterProcess(MonitoredProcess mp) {
		synchronized (mMonitoredProcesses) {
			mMonitoredProcesses.remove(mp);
		}
	}

	public void terminateExternalProcesses() {
		synchronized (mMonitoredProcesses) {
			for (MonitoredProcess mp : mMonitoredProcesses) {
				mp.forceShutdown();
			}
			mMonitoredProcesses.clear();
		}
	}

	/**
	 * Getter for the singleton instance. Plug-ins should always call this
	 * method to obtain a instance of UltimateServices. The core takes care that
	 * this instance is up to date.<br/>
	 * <br/>
	 * 
	 * All further functionality is provided as public instance methods by the
	 * returned instance.
	 * 
	 * @return the singleton instance of UltimateServices
	 */
	public static UltimateServices getInstance() {
		return s_Instance;
	}

	/**
	 * Creates the singleton instance. Should only be called by
	 * {@link UltimateCore}
	 * 
	 * @param application
	 *            the current instance of {@link UltimateCore}
	 */
	public static void createInstance(UltimateCore application) {
		s_Instance = new UltimateServices(null, application);
	}

	/**
	 * Sets the current ModelManager. Should only be called by
	 * {@link UltimateCore}
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
	public void persistExistingGraph(GraphType graph, boolean keepInMemory) throws StoreObjectException,
			GraphNotFoundException {
		this.m_ModelManager.persistExistingGraph(graph, keepInMemory);
	}

	/**
	 * Persists the existing graph in the {@link IModelManager}'s
	 * {@link IRepository}. Does not keep the model in memory
	 * 
	 * @see UltimateServices#persistExistingGraph(GraphType, boolean)
	 * @see IModelManager#persistAndDropExistingGraph(GraphType)
	 * @param graph
	 *            id of the model / graph to be persisted
	 * @throws StoreObjectException
	 *             if creating the persistent object failed
	 * @throws GraphNotFoundException
	 *             if there is no model with the specified model id in the
	 *             {@link IModelManager}
	 */
	public void persistExistingGraph(GraphType graph) throws StoreObjectException, GraphNotFoundException {
		this.m_ModelManager.persistAndDropExistingGraph(graph);
	}

	/**
	 * Gets the correct logger for an asking plug-in This method should be
	 * called by all plug-ins that extend {@link ITool} and by the Core Plugin
	 * and want to access their {@link Logger}. Appenders are set as defaults
	 * and log levels are set using preferences <br/>
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
		return UltimateLoggerFactory.getInstance().getLoggerById(pluginId);
	}

	/**
	 * Gets the correct logger for an asking external tool This method should be
	 * called by all external tools that want to access their {@link Logger}.
	 * Appenders are set as defaults and log levels are set using the
	 * preferences <br/>
	 * 
	 * Not to be used for plug-ins!
	 * 
	 * @param id
	 *            An identifier for the external tool that asks for its
	 *            {@link Logger}
	 * @return the log4j {@link Logger} for the external tool
	 */
	public Logger getLoggerForExternalTool(String id) {
		return UltimateLoggerFactory.getInstance().getLoggerById(CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX + id);
	}

	/**
	 * Gets the correct logger for the controller plug-in. This method should be
	 * called by all controller plug-ins that want to access their
	 * {@link Logger}. Appenders are set as defaults and log levels are set
	 * using the Eclipse IPreferenceStore <br/>
	 * 
	 * @return Logger for the current controller.
	 */
	public Logger getControllerLogger() {
		return UltimateLoggerFactory.getInstance().getLoggerById(UltimateLoggerFactory.LOGGER_NAME_CONTROLLER);
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
	 * @deprecated Will be removed as soon as all preference pages are
	 *             auto-generated. There will be no replacement! Tool management
	 *             is Core-duty
	 * @return a list of all active tools
	 */
	public List<ITool> getActiveTools() {
		return this.m_Application.getAllTools();
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

	/**
	 * Return true iff cancellation of toolchain is requested or deadline is
	 * exceeded.
	 */
	public boolean continueProcessing() {
		return this.m_Application.continueProcessing();
	}

	public void setSubtask(String task) {
		m_Application.setSubtask(task);
	}

	/**
	 * Set point in time where the toolchain should be stopped.
	 */
	public void setDeadline(long time) {
		m_Application.setDeadline(time);
	}

	/**
	 * Stop toolchain as soon as possible. Execution of the current toolchain
	 * will be canceled after the current plugin.
	 */
	public void cancelToolchain() {
		m_Application.cancelToolchain();
	}

	/**
	 * @return the m_ResultMap
	 */
	public HashMap<String, List<IResult>> getResultMap() {
		return this.m_ResultMap;
	}

	/**
	 * Clear all results for the next toolchain run
	 */
	public void initializeResultMap() {
		this.m_ResultMap = new HashMap<String, List<IResult>>();
	}

	/**
	 * This is the place to add a found Result to the global map.
	 * 
	 * @param id
	 *            the used plugin id.
	 * @param result
	 *            the found results.
	 */
	public void reportResult(String id, IResult result) {
		if (result instanceof IResultWithLocation) {
			if (((IResultWithLocation) result).getLocation() == null) {
				throw new IllegalArgumentException("Location is null");
			}
		}
		if (result.getShortDescription() == null) {
			throw new IllegalArgumentException("ShortDescription is null");
		}
		if (result.getLongDescription() == null) {
			throw new IllegalArgumentException("LongDescription is null");
		}
		List<IResult> list = this.m_ResultMap.get(id);
		if (list == null) {
			list = new ArrayList<IResult>();
		}
		list.add(result);
		m_ResultMap.put(id, list);
	}

	/**
	 * Workaround. Needed until Daniels ModelContainer is ready.
	 */
	@Deprecated
	public void initializeTranslatorSequence() {
		m_TranslatorSequence = new ArrayList<ITranslator<?, ?, ?, ?>>();
	}

	/**
	 * Workaround. Needed until Daniels ModelContainer is ready.
	 */
	@Deprecated
	public List<ITranslator<?, ?, ?, ?>> getTranslatorSequence() {
		return m_TranslatorSequence;
	}

	/**
	 * @return the identifierMapping
	 */
	public Map<String, String> getIdentifierMapping() {
		return identifierMapping;
	}

	/**
	 * @param identifierMapping
	 *            the identifierMapping to set
	 */
	public void setIdentifierMapping(Map<String, String> identifierMapping) {
		this.identifierMapping = identifierMapping;
	}

	/**
	 * Searches for a payload an element of the specified model.
	 * 
	 * @see IModelManager#search(GraphType, UltimateUID)
	 * @param modelId
	 *            the identifier of the model to be searched in
	 * @param id
	 *            the identifier of the element to be search for in the model
	 * @return Payload of the specified graph.
	 */
	public IPayload search(GraphType modelId, String id) {
		return this.m_ModelManager.search(modelId, id);
	}

	public IElement getModel(GraphType modelId) throws GraphNotFoundException {
		return this.m_ModelManager.getRootNode(modelId);
	}
}
