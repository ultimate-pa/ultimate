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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

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
import de.uni_freiburg.informatik.ultimate.ep.UltimateExtensionPoints;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * PluginFactory creates instances of plugins for toolchains and/or the core.
 *
 * @author dietsch
 *
 */
final class PluginFactory implements IServiceFactoryFactory {

	private static final Class<?>[] ITOOLCHAIN_PLUGIN_CLASSES =
			{ IAnalysis.class, IGenerator.class, IOutput.class, ISource.class };

	private final IExtensionRegistry mRegistry;
	private final ILogger mLogger;
	private final SettingsManager mSettingsManager;
	private final Map<Class<?>, List<IConfigurationElement>> mAvailableToolsByClass;
	private final Map<String, IConfigurationElement> mAvailableToolsByClassName;
	private final Map<String, String> mPluginIDToClassName;
	private final Map<Class<?>, IServiceFactory<?>> mAvailableServicesByClassName;

	private final Set<IConfigurationElement> mFailedTools;

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
		mFailedTools = new HashSet<>();
		mSettingsManager = settingsManager;

		mLogger.debug("--------------------------------------------------------------------------------");
		mLogger.debug("Detecting plugins...");
		registerType(IController.class);
		registerType(ISource.class);
		registerType(IOutput.class);
		registerType(IGenerator.class);
		registerType(IAnalysis.class);
		mController = loadControllerPlugin(mRegistry);
		mLogger.debug("Finished detecting plugins!");
		mLogger.debug("Loading services ...");
		registerType(IServiceFactory.class);
		mLogger.debug("Finished loading services!");
		mLogger.debug("--------------------------------------------------------------------------------");
	}

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

	List<String> getPluginIds() {
		return new ArrayList<>(mPluginIDToClassName.keySet());
	}

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
		mLogger.debug("--------------------------------------------------------------------------------");
		mLogger.debug("Loading all admissible plugins (creating one instance, loading preferences)");
		int notAdmissible = 0;
		final Set<String> pluginIds = new HashSet<>();
		for (final Class<?> type : ITOOLCHAIN_PLUGIN_CLASSES) {
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
					if (!pluginIds.add(tool.getPluginID())) {
						continue;
					}
					rtr.add(tool);
				} catch (final Exception ex) {
					mLogger.fatal("Exception during admissibility check of plugin " + elem.getName() + ": "
							+ ex.getMessage());
				}
			}
		}
		mLogger.debug("Finished loading " + rtr.size() + " admissible plugins"
				+ (notAdmissible > 0 ? " (" + notAdmissible + " not admissible)" : " (all were admissible)"));
		mLogger.debug("--------------------------------------------------------------------------------");
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
		// first, determine who will be the controller
		final List<IConfigurationElement> configElements = mAvailableToolsByClass.get(IController.class);

		if (configElements.isEmpty()) {
			mLogger.fatal(
					"Invalid configuration. You should have at least one IController plugin, but there are none.");
			return null;
		}

		if (configElements.size() == 1) {
			// just take the only one
			return loadControllerPlugin(configElements.get(0));
		}

		// ok, there are multiple ones. We have to see if they can be discriminated by their preference value
		final List<Pair<IConfigurationElement, Integer>> elemsWithPreference =
				configElements.stream().map(elem -> new Pair<>(elem, Integer.valueOf(elem.getAttribute("preference"))))
						.collect(Collectors.toList());

		final Optional<Pair<IConfigurationElement, Integer>> preferredElemOptional =
				elemsWithPreference.stream().min((a, b) -> a.getSecond().compareTo(b.getSecond()));
		if (!preferredElemOptional.isPresent()) {
			throw new AssertionError("Java8 is broken");
		}
		final Pair<IConfigurationElement, Integer> preferredElem = preferredElemOptional.get();
		final int minValue = preferredElem.getSecond();

		// check if the minimum is unambiguous
		final List<Pair<IConfigurationElement, Integer>> preferredElements =
				elemsWithPreference.stream().filter(a -> a.getSecond().equals(minValue)).collect(Collectors.toList());
		final int preferredElementsSize = preferredElements.size();
		if (preferredElementsSize == 1) {
			// it is, we take the preferred element.
			return loadControllerPlugin(preferredElem.getFirst());
		}
		// it is not, we have to give up

		mLogger.fatal("Invalid configuration. You should have only one preferred IController plugin, but you have "
				+ preferredElementsSize);
		for (final Pair<IConfigurationElement, Integer> elem : preferredElements) {
			mLogger.fatal(elem.getFirst().getAttribute("class") + " has preference value " + elem.getSecond());
		}
		return null;
	}

	private IController<RunDefinition> loadControllerPlugin(final IConfigurationElement controllerDescriptor) {
		final IController<RunDefinition> controller = createInstance(controllerDescriptor);
		mGuiMode = Boolean.valueOf(controllerDescriptor.getAttribute("isGraphical"));
		mSettingsManager.registerPlugin(controller);

		mLogger.debug("Loaded " + (mGuiMode ? "graphical " : "") + "controller " + controller.getPluginName());
		return controller;
	}

	@SuppressWarnings("unchecked")
	private <T extends IUltimatePlugin> T createInstance(final IConfigurationElement element) {
		if (element == null) {
			return null;
		}
		if (mFailedTools.contains(element)) {
			mLogger.warn("Will not retry already failed Ultimate plugin " + element.getAttribute("class"));
			return null;
		}
		try {
			return (T) element.createExecutableExtension("class");
		} catch (final CoreException ex) {
			mLogger.fatal("Exception during instantiation of Ultimate plugin " + element.getAttribute("class"), ex);
			mFailedTools.add(element);
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

					registerClassAndAllInterfaces(myClass, factory);
				} catch (final ClassNotFoundException e) {
					mLogger.fatal("Cannot register type: " + e);
				}
			}
			mLogger.debug(mAvailableServicesByClassName.size() + " " + clazz.getSimpleName() + " services available");
		} else {
			registerTool(clazz);
		}
	}

	private void registerClassAndAllInterfaces(final Class<?> myClass, final IServiceFactory<?> factory) {
		// first, register the actual class
		mAvailableServicesByClassName.put(myClass, factory);

		for (final Class<?> clazzInterface : myClass.getInterfaces()) {
			if (clazzInterface.equals(IServiceFactory.class)) {
				// everyone implements this, skip it
				continue;
			}
			registerClassAndAllInterfaces(clazzInterface, factory);
		}

	}

	private void registerTool(final Class<?> clazz) {
		final List<IConfigurationElement> result = new ArrayList<>();
		mAvailableToolsByClass.put(clazz, result);
		for (final IConfigurationElement element : mRegistry
				.getConfigurationElementsFor(getExtensionPointFromClass(clazz))) {
			result.add(element);
			final String className = element.getAttribute("class");
			mAvailableToolsByClassName.put(className, element);
			mPluginIDToClassName.put(createPluginID(className), className);
		}
		mLogger.debug(result.size() + " " + clazz.getSimpleName() + " plugins available");
	}

	private static String createPluginID(final String classname) {
		final String rtr = classname.substring(0, classname.lastIndexOf('.'));
		return rtr;
	}

	private static String getExtensionPointFromClass(final Class<?> clazz) {
		final String qualifiedName = clazz.getName();
		switch (qualifiedName) {
		case "de.uni_freiburg.informatik.ultimate.core.model.IController":
			return UltimateExtensionPoints.EP_CONTROLLER;
		case "de.uni_freiburg.informatik.ultimate.core.model.ISource":
			return UltimateExtensionPoints.EP_SOURCE;
		case "de.uni_freiburg.informatik.ultimate.core.model.IOutput":
			return UltimateExtensionPoints.EP_OUTPUT;
		case "de.uni_freiburg.informatik.ultimate.core.model.IGenerator":
			return UltimateExtensionPoints.EP_GENERATOR;
		case "de.uni_freiburg.informatik.ultimate.core.model.IAnalysis":
			return UltimateExtensionPoints.EP_ANALYSIS;
		case "de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory":
			return UltimateExtensionPoints.EP_SERVICE;
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
