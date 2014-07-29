package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchainPlugin;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;

/**
 * 
 * PluginFactory creates instances of plugins for toolchains and/or the core.
 * 
 * @author dietsch
 * 
 */
final class PluginFactory implements IServiceFactoryFactory {

	// private static final Class<?>[] sIToolClasses = { IAnalysis.class,
	// IGenerator.class, IOutput.class };
	private static final Class<?>[] sIToolchainPluginClasses = { IAnalysis.class, IGenerator.class, IOutput.class,
			ISource.class };

	private final IExtensionRegistry mRegistry;
	private final Logger mLogger;
	private final SettingsManager mSettingsManager;
	private final HashMap<Class<?>, List<IConfigurationElement>> mAvailableToolsByClass;
	private final HashMap<String, IConfigurationElement> mAvailableToolsByClassName;
	private final HashMap<String, String> mPluginIDToClassName;
	private final HashMap<Class<?>, IServiceFactory<?>> mAvailableServicesByClassName;

	private boolean mGuiMode;
	private IController mController;
	private List<IToolchainPlugin> mToolchainPluginCache;
	private List<ITool> mToolCache;

	PluginFactory(SettingsManager settingsManager, Logger logger) {
		mLogger = logger;
		mRegistry = Platform.getExtensionRegistry();
		mAvailableToolsByClass = new HashMap<>();
		mAvailableToolsByClassName = new HashMap<>();
		mPluginIDToClassName = new HashMap<>();
		mAvailableServicesByClassName = new HashMap<>();
		mSettingsManager = settingsManager;

		mLogger.info("--------------------------------------------------------------------------------");
		mLogger.info("Detecting plugins...");
		registerType(IController.class);
		registerType(ISource.class);
		registerType(IOutput.class);
		registerType(IGenerator.class);
		registerType(IAnalysis.class);
		mController = loadControllerPlugin(mRegistry);
		mLogger.info("Finished detecting plugins!");
		mLogger.info("Loading services ...");
		registerType(IServiceFactory.class);
		mLogger.info("Finished loading services!");
		mLogger.info("--------------------------------------------------------------------------------");
	}

	// TODO: Do it somewhere else
	// mLogger.debug("--------------------------------------------------------------------------------");
	// mLogger.debug("Loaded default settings");
	// checkPreferencesForActivePlugins();
	// mLogger.debug("--------------------------------------------------------------------------------");

	IController getController() {
		return mController;
	}

	List<String> getPluginClassNames(Class<?> clazz) {
		List<IConfigurationElement> elems = mAvailableToolsByClass.get(clazz);
		List<String> rtr = new ArrayList<>();
		if (elems != null) {
			for (IConfigurationElement elem : elems) {
				rtr.add(elem.getAttribute("class"));
			}
		}
		return rtr;
	}

	/**
	 * 
	 * TODO: How to check feasibility / admissibility ?
	 * 
	 * @return
	 */
	List<String> getPluginIds() {
		return new ArrayList<>(mPluginIDToClassName.keySet());
	}

	/**
	 * 
	 * @param toolId
	 * @return
	 */
	<T extends IToolchainPlugin> T createTool(String toolId) {
		IConfigurationElement element = mAvailableToolsByClassName.get(toolId);
		if (element == null) {
			// maybe the user used the PluginID?
			element = mAvailableToolsByClassName.get(mPluginIDToClassName.get(toolId));
		}
		T plugin = createInstance(element);
		return prepareToolchainPlugin(plugin);
	}

	private <T extends IToolchainPlugin> T prepareToolchainPlugin(T plugin) {
		if (plugin == null) {
			return null;
		}

		if (plugin instanceof ITool) {
			ITool tool = (ITool) plugin;
			if (tool.isGuiRequired() && !mGuiMode) {
				mLogger.error("Cannot load plugin " + tool.getPluginID() + ": Requires GUI controller");
				return null;
			}
		}
		mSettingsManager.checkPreferencesForActivePlugins(plugin.getPluginID(), plugin.getPluginName());
		return plugin;
	}

	/**
	 * This method returns a list of instances of available IToolchainPlugins.
	 * Those tools are not initialized.
	 * 
	 * @return
	 */
	List<IToolchainPlugin> getAllAvailableToolchainPlugins() {
		List<IToolchainPlugin> rtr;
		if (mToolchainPluginCache != null) {
			rtr = new ArrayList<>();
			rtr.addAll(mToolchainPluginCache);
			return rtr;
		}
		rtr = loadAdmissiblePlugins();
		mToolchainPluginCache = new ArrayList<>();
		mToolchainPluginCache.addAll(rtr);
		return rtr;
	}

	List<ITool> getAllAvailableTools() {
		List<ITool> rtr = new ArrayList<>();
		if (mToolCache != null) {
			rtr.addAll(mToolCache);
			return rtr;
		}
		for (IToolchainPlugin plugin : getAllAvailableToolchainPlugins()) {
			// TODO: This may be misleading, as direct subclasses of ITool are
			// not applicable here
			if (plugin instanceof ITool) {
				rtr.add((ITool) plugin);
			}
		}
		mToolchainPluginCache = new ArrayList<>();
		mToolchainPluginCache.addAll(rtr);
		return rtr;
	}

	private List<IToolchainPlugin> loadAdmissiblePlugins() {
		List<IToolchainPlugin> rtr = new ArrayList<>();
		mLogger.info("--------------------------------------------------------------------------------");
		mLogger.info("Loading all admissible plugins (creating one instance, loading preferences)");
		int notAdmissible = 0;
		for (Class<?> type : sIToolchainPluginClasses) {
			List<IConfigurationElement> elements = mAvailableToolsByClass.get(type);
			if (elements == null) {
				continue;
			}
			for (IConfigurationElement elem : elements) {
				IToolchainPlugin tool = (IToolchainPlugin) createInstance(elem);
				tool = prepareToolchainPlugin(tool);
				if (tool == null) {
					notAdmissible++;
					continue;
				}
				rtr.add(tool);
			}
		}
		mLogger.info("Finished loading " + rtr.size() + " admissible plugins"
				+ (notAdmissible > 0 ? " (" + notAdmissible + " not admissible)" : " (all were admissible)"));
		mLogger.info("--------------------------------------------------------------------------------");
		return rtr;
	}

	boolean isPluginAvailable(String pluginId) {
		return mAvailableToolsByClassName.containsKey(pluginId) || mPluginIDToClassName.containsKey(pluginId);
	}

	/**
	 * This method loads all contributions to the IController Extension Point.
	 * Its receiving configuration elements (see exsd-files) which define class
	 * name in element "impl" and attribute "class" as well as an attribute
	 * "isGraphical". It then
	 * 
	 * Changed in Ultimate 2.0 to support multiple present controllers and to
	 * make the distinction between graphical and non graphical ones
	 * 
	 * @param reg
	 *            The extension registry (which extensions are valid and how can
	 *            I find them); is obtained by Platform.getExtensionRegistry()
	 * @throws CoreException
	 */
	private IController loadControllerPlugin(IExtensionRegistry reg) {
		List<IConfigurationElement> configElements = mAvailableToolsByClass.get(IController.class);

		if (configElements.size() != 1) {
			mLogger.fatal("Invalid configuration. You should have only 1 IController plugin, but you have "
					+ configElements.size());

			if (configElements.size() == 0) {
				return null;
			}

			for (IConfigurationElement elem : configElements) {
				mLogger.fatal(elem.getAttribute("class"));
			}
			return null;
		}
		IConfigurationElement controllerDescriptor = configElements.get(0);
		IController controller = createInstance(controllerDescriptor);
		mGuiMode = new Boolean(controllerDescriptor.getAttribute("isGraphical")).booleanValue();
		mSettingsManager.checkPreferencesForActivePlugins(controller.getPluginID(), controller.getPluginName());

		mLogger.info("Loaded " + (mGuiMode ? "graphical" : "") + " controller " + controller.getPluginName());
		return controller;
	}

	@SuppressWarnings("unchecked")
	private <T extends IUltimatePlugin> T createInstance(IConfigurationElement element) {
		if (element == null) {
			return null;
		}
		try {
			return (T) element.createExecutableExtension("class");
		} catch (CoreException ex) {
			mLogger.fatal("Exception during instantiation of ultimate plugin " + element.getAttribute("class"), ex);
			return null;
		}
	}

	private void registerType(Class<?> clazz) {
		if (clazz.equals(IServiceFactory.class)) {
			for (IConfigurationElement element : mRegistry
					.getConfigurationElementsFor(getExtensionPointFromClass(clazz))) {
				String className = element.getAttribute("class");
				try {
					Class<?> myClass = Class.forName(className);
					IServiceFactory<?> factory = createInstance(element);
					mSettingsManager.checkPreferencesForActivePlugins(factory.getPluginID(), factory.getPluginName());
					mAvailableServicesByClassName.put(myClass, factory);
				} catch (ClassNotFoundException e) {
					e.printStackTrace();
				}
			}
			mLogger.info(mAvailableServicesByClassName.size() + " " + clazz.getSimpleName() + " services available");
		} else {
			registerTool(clazz);
		}
	}

	private void registerTool(Class<?> clazz) {
		List<IConfigurationElement> result = new ArrayList<IConfigurationElement>();
		mAvailableToolsByClass.put(clazz, result);
		for (IConfigurationElement element : mRegistry.getConfigurationElementsFor(getExtensionPointFromClass(clazz))) {
			result.add(element);
			String className = element.getAttribute("class");
			mAvailableToolsByClassName.put(className, element);
			mPluginIDToClassName.put(createPluginID(className), className);
		}
		mLogger.info(result.size() + " " + clazz.getSimpleName() + " plugins available");
	}

	private String createPluginID(String classname) {
		String rtr = classname.substring(0, classname.lastIndexOf("."));
		return rtr;
	}

	private String getExtensionPointFromClass(Class<?> clazz) {
		String qualifiedName = clazz.getName();
		switch (qualifiedName) {
		case "de.uni_freiburg.informatik.ultimate.ep.interfaces.IController":
			return ExtensionPoints.EP_CONTROLLER;
		case "de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource":
			return ExtensionPoints.EP_SOURCE;
		case "de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput":
			return ExtensionPoints.EP_OUTPUT;
		case "de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator":
			return ExtensionPoints.EP_GENERATOR;
		case "de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis":
			return ExtensionPoints.EP_ANALYSIS;
		case "de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory":
			return ExtensionPoints.EP_SERVICE;
		default:
			throw new IllegalArgumentException();
		}
	}

	public <T, K extends IServiceFactory<T>> T createService(Class<K> service, IUltimateServiceProvider services,
			IToolchainStorage storage) {
		IServiceFactory<?> unknownfactory = mAvailableServicesByClassName.get(service);

		if (unknownfactory == null) {
			return null;
		}

		IServiceFactory<T> factory = service.cast(unknownfactory);

		T rtr = factory.createInstance(services, storage);
		return rtr;
	}
}
