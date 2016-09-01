/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainPlugin;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;

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
	private static final Class<?>[] sIToolchainPluginClasses =
			{ IAnalysis.class, IGenerator.class, IOutput.class, ISource.class };

	private final IExtensionRegistry mRegistry;
	private final ILogger mLogger;
	private final SettingsManager mSettingsManager;
	private final HashMap<Class<?>, List<IConfigurationElement>> mAvailableToolsByClass;
	private final HashMap<String, IConfigurationElement> mAvailableToolsByClassName;
	private final HashMap<String, String> mPluginIDToClassName;
	private final HashMap<Class<?>, IServiceFactory<?>> mAvailableServicesByClassName;

	private boolean mGuiMode;
	private final IController<RunDefinition> mController;
	private List<IToolchainPlugin> mToolchainPluginCache;
	private List<ITool> mToolCache;

	PluginFactory(final SettingsManager settingsManager, final ILogger logger) {
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

	IController<RunDefinition> getController() {
		return mController;
	}

	List<String> getPluginClassNames(final Class<?> clazz) {
		final List<IConfigurationElement> elems = mAvailableToolsByClass.get(clazz);
		final List<String> rtr = new ArrayList<>();
		if (elems != null) {
			for (final IConfigurationElement elem : elems) {
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
	<T extends IToolchainPlugin> T createTool(final String toolId) {
		IConfigurationElement element = mAvailableToolsByClassName.get(toolId);
		if (element == null) {
			// maybe the user used the PluginID?
			element = mAvailableToolsByClassName.get(mPluginIDToClassName.get(toolId));
		}
		final T plugin = createInstance(element);
		return prepareToolchainPlugin(plugin);
	}

	private <T extends IToolchainPlugin> T prepareToolchainPlugin(final T plugin) {
		if (plugin == null) {
			return null;
		}

		if (plugin instanceof ITool) {
			final ITool tool = (ITool) plugin;
			if (tool.isGuiRequired() && !mGuiMode) {
				mLogger.error("Cannot load plugin " + tool.getPluginID() + ": Requires GUI controller");
				return null;
			}
		}
		mSettingsManager.registerPlugin(plugin);
		return plugin;
	}

	/**
	 * This method returns a list of instances of available IToolchainPlugins. Those tools are not initialized.
	 *
	 * @return
	 */
	List<IToolchainPlugin> getAllAvailableToolchainPlugins() {
		if (mToolchainPluginCache == null) {
			mToolchainPluginCache = loadAdmissiblePlugins();
		}
		final List<IToolchainPlugin> rtr = new ArrayList<>();
		rtr.addAll(mToolchainPluginCache);
		return rtr;
	}

	List<ITool> getAllAvailableTools() {
		final List<ITool> rtr = new ArrayList<>();
		if (mToolCache != null) {
			rtr.addAll(mToolCache);
			return rtr;
		}
		for (final IToolchainPlugin plugin : getAllAvailableToolchainPlugins()) {
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
		final List<IToolchainPlugin> rtr = new ArrayList<>();
		mLogger.info("--------------------------------------------------------------------------------");
		mLogger.info("Loading all admissible plugins (creating one instance, loading preferences)");
		int notAdmissible = 0;
		for (final Class<?> type : sIToolchainPluginClasses) {
			final List<IConfigurationElement> elements = mAvailableToolsByClass.get(type);
			if (elements == null) {
				continue;
			}
			for (final IConfigurationElement elem : elements) {
				try {
					final IToolchainPlugin tool = prepareToolchainPlugin((IToolchainPlugin) createInstance(elem));
					if (tool == null) {
						notAdmissible++;
						continue;
					}
					rtr.add(tool);
				} catch (final Exception ex) {
					mLogger.fatal("Exception during admissibility check of plugin " + elem.getName() + ": "
							+ ex.getMessage());
				}
			}
		}
		mLogger.info("Finished loading " + rtr.size() + " admissible plugins"
				+ (notAdmissible > 0 ? " (" + notAdmissible + " not admissible)" : " (all were admissible)"));
		mLogger.info("--------------------------------------------------------------------------------");
		return rtr;
	}

	boolean isPluginAvailable(final String pluginId) {
		return mAvailableToolsByClassName.containsKey(pluginId) || mPluginIDToClassName.containsKey(pluginId);
	}

	/**
	 * This method loads all contributions to the IController Extension Point. Its receiving configuration elements (see
	 * exsd-files) which define class name in element "impl" and attribute "class" as well as an attribute
	 * "isGraphical". It then
	 *
	 * Changed in Ultimate 2.0 to support multiple present controllers and to make the distinction between graphical and
	 * non graphical ones
	 *
	 * @param reg
	 *            The extension registry (which extensions are valid and how can I find them); is obtained by
	 *            Platform.getExtensionRegistry()
	 * @throws CoreException
	 */
	private IController<RunDefinition> loadControllerPlugin(final IExtensionRegistry reg) {
		final List<IConfigurationElement> configElements = mAvailableToolsByClass.get(IController.class);

		if (configElements.size() != 1) {
			mLogger.fatal("Invalid configuration. You should have only 1 IController plugin, but you have "
					+ configElements.size());

			if (configElements.size() == 0) {
				return null;
			}

			for (final IConfigurationElement elem : configElements) {
				mLogger.fatal(elem.getAttribute("class"));
			}
			return null;
		}
		final IConfigurationElement controllerDescriptor = configElements.get(0);
		final IController<RunDefinition> controller = createInstance(controllerDescriptor);
		mGuiMode = new Boolean(controllerDescriptor.getAttribute("isGraphical")).booleanValue();
		mSettingsManager.registerPlugin(controller);

		mLogger.info("Loaded " + (mGuiMode ? "graphical " : "") + "controller " + controller.getPluginName());
		return controller;
	}

	@SuppressWarnings("unchecked")
	private <T extends IUltimatePlugin> T createInstance(final IConfigurationElement element) {
		if (element == null) {
			return null;
		}
		try {
			return (T) element.createExecutableExtension("class");
		} catch (final CoreException ex) {
			mLogger.fatal("Exception during instantiation of ultimate plugin " + element.getAttribute("class"), ex);
			return null;
		}
	}

	private void registerType(final Class<?> clazz) {
		if (clazz.equals(IServiceFactory.class)) {
			for (final IConfigurationElement element : mRegistry
					.getConfigurationElementsFor(getExtensionPointFromClass(clazz))) {
				final String className = element.getAttribute("class");
				try {
					final Class<?> myClass = Class.forName(className);
					final IServiceFactory<?> factory = createInstance(element);
					mSettingsManager.registerPlugin(factory);
					mAvailableServicesByClassName.put(myClass, factory);
				} catch (final ClassNotFoundException e) {
					e.printStackTrace();
				}
			}
			mLogger.info(mAvailableServicesByClassName.size() + " " + clazz.getSimpleName() + " services available");
		} else {
			registerTool(clazz);
		}
	}

	private void registerTool(final Class<?> clazz) {
		final List<IConfigurationElement> result = new ArrayList<IConfigurationElement>();
		mAvailableToolsByClass.put(clazz, result);
		for (final IConfigurationElement element : mRegistry
				.getConfigurationElementsFor(getExtensionPointFromClass(clazz))) {
			result.add(element);
			final String className = element.getAttribute("class");
			mAvailableToolsByClassName.put(className, element);
			mPluginIDToClassName.put(createPluginID(className), className);
		}
		mLogger.info(result.size() + " " + clazz.getSimpleName() + " plugins available");
	}

	private String createPluginID(final String classname) {
		final String rtr = classname.substring(0, classname.lastIndexOf("."));
		return rtr;
	}

	private String getExtensionPointFromClass(final Class<?> clazz) {
		final String qualifiedName = clazz.getName();
		switch (qualifiedName) {
		case "de.uni_freiburg.informatik.ultimate.core.model.IController":
			return ExtensionPoints.EP_CONTROLLER;
		case "de.uni_freiburg.informatik.ultimate.core.model.ISource":
			return ExtensionPoints.EP_SOURCE;
		case "de.uni_freiburg.informatik.ultimate.core.model.IOutput":
			return ExtensionPoints.EP_OUTPUT;
		case "de.uni_freiburg.informatik.ultimate.core.model.IGenerator":
			return ExtensionPoints.EP_GENERATOR;
		case "de.uni_freiburg.informatik.ultimate.core.model.IAnalysis":
			return ExtensionPoints.EP_ANALYSIS;
		case "de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory":
			return ExtensionPoints.EP_SERVICE;
		default:
			throw new IllegalArgumentException();
		}
	}

	@Override
	public <T, K extends IServiceFactory<T>> T createService(final Class<K> service,
			final IUltimateServiceProvider services, final IToolchainStorage storage) {
		final IServiceFactory<?> unknownfactory = mAvailableServicesByClassName.get(service);

		if (unknownfactory == null) {
			return null;
		}

		final IServiceFactory<T> factory = service.cast(unknownfactory);

		final T rtr = factory.createInstance(services, storage);
		return rtr;
	}
}
