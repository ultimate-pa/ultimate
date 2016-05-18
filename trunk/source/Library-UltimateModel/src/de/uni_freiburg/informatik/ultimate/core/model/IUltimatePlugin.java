/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;

/**
 * An IUltimatePlugin describes the most basic interface for all plugins that
 * together form the Ultimate ecosystem.
 * 
 * The methods at this level are used to provide
 * <ul>
 * <li>Different log levels for different plugins via preferences in the core</li>
 * <li>The ability to define preferences per plugin that can be changed by the
 * user</li>
 * </ul>
 * 
 * 
 * TODO: Currently, preferences are only loaded for implementers of of
 * {@link IController}, {@link ICore} and {@link IToolchainPlugin}! Library
 * plugins that implement this interface directly are out of luck! The current
 * intention is that library plugins do not implement any of the cores
 * interfaces (subject to change)<br>
 * <br>
 * Clients should subclass this interface if they want to define a library
 * plugin. For toolchain plugins (i.e. the regular Ultimate plugins) see
 * {@link IToolchainPlugin}.
 * 
 * @author dietsch
 */
public interface IUltimatePlugin {
	/**
	 * 
	 * @return Returns a human-readable name for the plugin. This will be shown
	 *         in the user interface and in most logs.
	 */
	String getPluginName();

	/**
	 * Returns the name of the package of the implementing class as per the Java
	 * Language Specification. You can get that name for example with
	 * {@code getClass().getPackage().getName()} or, e.g.,
	 * {@code JungVisualization.class.getPackage().getName()}. <br>
	 * <br>
	 * The correct implementation of this interface also requires that
	 * implementers must use the string provided here (case-sensitive) as
	 * <ul>
	 * <li>{@code Bundle-SymbolicName} in the plugin's MANIFEST.MF</li>
	 * <li>{@code <artifactId>} in the plugin's pom.xml</li>
	 * <li>{@code id} in feature.xml files used to include this plugin in build
	 * features (i.e. BA_FeatureUltimate...)</li>
	 * <li>After performing those changes and recompiling, you may have to resync your Launch Configurations</li>
	 * </ul>
	 * 
	 * Implementers of {@link ICore} and {@link IController} have to take
	 * additional steps: TODO: Describe additional steps
	 * 
	 * @return The name of the namespace of the implementing class.
	 */
	String getPluginID();

	/**
	 * Is used by preference-changing {@link IController controllers} to
	 * enumerate all available preferences of {@link # IUltimatePlugins} in
	 * order to provide interfaces for users.
	 * 
	 * @return If a plugin uses preferences, it should return its preference
	 *         initializer here. If not, it should return null.
	 */
	IPreferenceInitializer getPreferences();
}
