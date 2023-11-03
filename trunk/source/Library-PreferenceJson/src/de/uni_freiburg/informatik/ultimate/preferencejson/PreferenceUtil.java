/*
 * Copyright (C) 2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.preferencejson;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.stream.Collectors;

import com.google.gson.Gson;

import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class PreferenceUtil {

	private static final String PLUGIN_ID_CORE = "de.uni_freiburg.informatik.ultimate.core";

	private PreferenceUtil() {
		// do not instantiate utility class
	}

	/**
	 * Convert the label of an {@link UltimatePreferenceItem} to a unique string that contains the plugin id, no spaces,
	 * and no special symbols.
	 */
	public static String convertLabelToLongName(final String pluginId, final UltimatePreferenceItem<?> item) {
		return convertLabelToLongName(pluginId, item.getLabel());
	}

	/**
	 * Convert the label of an {@link UltimatePreferenceItem} to a unique string that contains the plugin id, no spaces,
	 * and no special symbols.
	 */
	public static String convertLabelToLongName(final String pluginId, final String label) {
		final int lastIdx = pluginId.lastIndexOf('.');
		final String prefix = lastIdx > 0 ? pluginId.substring(lastIdx + 1) : pluginId;
		final String unprocessedName = prefix + " " + label;
		final String replaced =
				unprocessedName.replace(":", "").replaceAll("[ ()\"'.]+", ".").toLowerCase(Locale.ENGLISH);
		if (replaced.endsWith(".")) {
			// prevent label ending with '.'
			return replaced.substring(0, replaced.length() - 1);
		}
		return replaced;
	}

	/**
	 * Generate a JSON representation of all default settings provided by Ultimate that can be used by the web frontend
	 * as user settings.
	 */
	public static String generateFrontendSettingsJsonFromDefaultSettings(final ICore<?> core) {
		return generateFrontendSettingsJson(core, getDefaultSettings(core));
	}

	/**
	 * Generate a JSON representation of all settings provided by Ultimate that differ from their defaults. The JSON
	 * representation can be used by the web frontend as user settings.
	 */
	public static String generateFrontendSettingsJsonFromDeltaSettings(final IUltimateServiceProvider services,
			final ICore<?> core) {
		return generateFrontendSettingsJson(core, getDeltaSettings(services, core));
	}

	/**
	 * Generate a JSON representation of all default settings provided by Ultimate that can be used by the web backend
	 * as whitelist.
	 */
	public static String generateBackendWhitelistJsonFromDefaultSettings(final ICore<?> core) {
		return generateBackendWhitelistJson(getDefaultSettings(core));
	}

	/**
	 * Generate a JSON representation of all settings provided by Ultimate that differ from their defaults. The JSON
	 * representation can be used by the web backend as whitelist.
	 */
	public static String generateBackendWhitelistJsonFromDeltaSettings(final IUltimateServiceProvider services,
			final ICore<?> core) {
		return generateBackendWhitelistJson(getDeltaSettings(services, core));
	}

	private static String generateFrontendSettingsJson(final ICore<?> core,
			final Map<String, Map<String, Object>> settings) {
		final Map<String, List<Map<String, Object>>> jsonAsPoJ = new LinkedHashMap<>(1);
		final List<Map<String, Object>> frontendSettings = new ArrayList<>();
		jsonAsPoJ.put("frontend_settings", frontendSettings);

		final Map<String, IUltimatePlugin> plugins = Arrays.stream(core.getRegisteredUltimatePlugins())
				.collect(Collectors.toMap(IUltimatePlugin::getPluginID, a -> a));

		for (final Entry<String, Map<String, Object>> pluginSettings : settings.entrySet()) {
			if (pluginSettings.getValue().isEmpty()) {
				continue;
			}
			final IUltimatePlugin plugin = plugins.get(pluginSettings.getKey());

			final Map<String, UltimatePreferenceItem<?>> pluginPreferenceItems =
					BaseUltimatePreferenceItem.constructFlattenedList(plugin.getPreferences().getPreferenceItems())
							.stream().filter(a -> a.getType() != PreferenceType.Label)
							.collect(Collectors.toMap(UltimatePreferenceItem::getLabel, a -> a));

			for (final Entry<String, Object> setting : pluginSettings.getValue().entrySet()) {
				final UltimatePreferenceItem<?> item = pluginPreferenceItems.get(setting.getKey());
				if (item == null) {
					final ILogger logger = core.getCoreLoggingService().getLogger(PreferenceUtil.class);
					logger.error("%s '%s' is not a valid setting (perhaps renamed?)", plugin.getPluginID(),
							setting.getKey());
					continue;
				}
				frontendSettings.add(
						createFrontendSetting(pluginSettings.getKey(), setting.getKey(), setting.getValue(), item));
			}
		}

		return new Gson().toJson(jsonAsPoJ);
	}

	private static String generateBackendWhitelistJson(final Map<String, Map<String, Object>> settings) {
		final Map<String, List<String>> jsonAsPoJ = new LinkedHashMap<>();
		for (final Entry<String, Map<String, Object>> pluginSettings : settings.entrySet()) {
			if (pluginSettings.getValue().isEmpty()) {
				continue;
			}
			jsonAsPoJ.put(pluginSettings.getKey(),
					pluginSettings.getValue().keySet().stream().collect(Collectors.toUnmodifiableList()));
		}
		return new Gson().toJson(jsonAsPoJ);
	}

	/**
	 * @return Ultimate settings that differ from the defaults
	 */
	private static Map<String, Map<String, Object>> getDeltaSettings(final IUltimateServiceProvider services,
			final ICore<?> core) {
		final Map<String, Map<String, Object>> defaults = getDefaultSettings(core);
		final Map<String, Map<String, Object>> current = getCurrentSettings(services, core);
		final Map<String, Map<String, Object>> rtr = new LinkedHashMap<>();

		for (final Entry<String, Map<String, Object>> plugin : current.entrySet()) {
			final Map<String, Object> pluginCurrent = plugin.getValue();
			if (pluginCurrent.isEmpty()) {
				continue;
			}
			final Map<String, Object> pluginDefault = defaults.get(plugin.getKey());
			final Map<String, Object> pluginDelta = new LinkedHashMap<>();
			for (final Entry<String, Object> entry : pluginCurrent.entrySet()) {
				if (!Objects.equals(entry.getValue(), pluginDefault.get(entry.getKey()))) {
					pluginDelta.put(entry.getKey(), entry.getValue());
				}
			}
			rtr.put(plugin.getKey(), pluginDelta);
		}
		return rtr;
	}

	private static Map<String, Map<String, Object>> getDefaultSettings(final ICore<?> core) {
		final Map<String, Map<String, Object>> rtr = new LinkedHashMap<>();

		for (final String pluginId : core.getRegisteredUltimatePluginIDs()) {
			final IPreferenceProvider prefProvider = core.getPreferenceProvider(pluginId);
			final Map<String, Object> defaultPrefs = prefProvider.getDefaultPreferences();
			final Map<String, Object> old = rtr.put(pluginId, defaultPrefs);
			if (old != null) {
				throw new IllegalStateException(String.format("Plugin %s is registered twice", pluginId));
			}
		}
		rtr.put(PLUGIN_ID_CORE, core.getPreferenceProvider(PLUGIN_ID_CORE).getDefaultPreferences());
		return rtr;
	}

	private static Map<String, Map<String, Object>> getCurrentSettings(final IUltimateServiceProvider services,
			final ICore<?> core) {
		final Map<String, Map<String, Object>> rtr = new LinkedHashMap<>();

		for (final String pluginId : core.getRegisteredUltimatePluginIDs()) {
			final IPreferenceProvider prefProvider = services.getPreferenceProvider(pluginId);
			final Map<String, Object> currentPrefs = prefProvider.getPreferences();
			final Map<String, Object> old = rtr.put(pluginId, currentPrefs);
			if (old != null) {
				throw new IllegalStateException(String.format("Plugin %s is registered twice", pluginId));
			}
		}
		rtr.put(PLUGIN_ID_CORE, core.getPreferenceProvider(PLUGIN_ID_CORE).getPreferences());
		return rtr;
	}

	/**
	 * Generates a list of settings, where each setting is represented as a map. This java data structure can then be
	 * converted to JSON to obtain the <tt>frontend_settings</tt> value in <tt>config.js</tt>.
	 * 
	 * Each map has the following entries.
	 * <p>
	 * <ul>
	 * <li><tt>plugin_id</tt>: The Ultimate plugin ID</li>
	 * <li><tt>key</tt>: Ultimate key to lookup the setting</li>
	 * <li><tt>id</tt>: A mandatory unique id for this setting (generated from key and plugin_id) that is used to lookup
	 * UI elements generated from settings</li>
	 * <li><tt>name</tt>: Settings name displayed in the settings menu (identical to key)</li>
	 * <li><tt>type</tt>: One of "bool", "int", "string", or "real". Used in the frontend for sliders, checkboxes,
	 * etc.</li>
	 * <li><tt>default</tt>: A default value for the setting. The method converts <tt>defaultValue</tt> to a primitive
	 * compatible with the type above.</li>
	 * <li><tt>visible</tt>: A boolean that controls whether this option is visible in the frontend. Is set to
	 * false.</li>
	 * <li>Optional: <tt>range</tt>: A list of integers representing a minimal and a maximal value, e.g.
	 * <tt>[1,12]</tt>. If the type is int or real, this allows the frontend to generate a slider control.</li>
	 * <li>Optional: <tt>options</tt>: A list of strings representing values to choose from. If the type is string, this
	 * allows the frontend to generate a selection box.</li>
	 * </ul>
	 *
	 * @param item
	 * 
	 */
	private static Map<String, Object> createFrontendSetting(final String pluginId, final String key,
			final Object value, final UltimatePreferenceItem<?> item) {
		final Map<String, Object> rtr = new HashMap<>(8);
		rtr.put("plugin_id", pluginId);
		rtr.put("key", key);
		rtr.put("id", convertLabelToLongName(pluginId, key).replace('.', '_'));
		rtr.put("name", key);
		rtr.put("visible", false);

		rtr.put("default", getFrontendSettingsValue(item, value));
		rtr.put("type", getFrontendSettingsType(item));

		if (item.getType() == PreferenceType.Radio || item.getType() == PreferenceType.Combo) {
			rtr.put("options", Arrays.asList(item.getChoices()));
		}

		// TODO: Perhaps handle ranges via item.getPreferenceValidator() as well
		// TODO: Deal with keyvalue types

		return rtr;
	}

	private static Object getFrontendSettingsValue(final UltimatePreferenceItem<?> item, final Object value) {
		switch (item.getType()) {
		case Boolean:
			return Boolean.valueOf(value.toString());
		case Double:
			return Double.valueOf(value.toString());
		case Integer:
			return Integer.valueOf(value.toString());
		case Color:
		case Combo:
		case Directory:
		case File:
		case KeyValue:
		case Label:
		case MultilineString:
		case Path:
		case Radio:
		case String:
		case SubItemContainer:
		default:
			return value;
		}
	}

	private static String getFrontendSettingsType(final UltimatePreferenceItem<?> item) {
		switch (item.getType()) {
		case Boolean:
			return "bool";
		case Double:
			return "real";
		case Integer:
			return "int";
		case Color:
		case Combo:
		case Directory:
		case File:
		case Label:
		case MultilineString:
		case Path:
		case Radio:
		case String:
		case SubItemContainer:
		case KeyValue:
		default:
			return "string";

		}
	}
}
