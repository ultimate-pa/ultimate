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

import java.io.FileNotFoundException;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This interface describes the object that is passed to {@link IController#init(ICore, ILoggingService)}.
 *
 * {@link IController} should use at least {@link #requestToolchain()} and {@link #releaseToolchain(IToolchain)} to
 * receive {@link IToolchain} instances through which Ultimate is actually controlled.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ICore<T> {

	/**
	 * Create a toolchain data instance describing a to-be created toolchain using a path to an XML file defining this
	 * toolchain.
	 *
	 * @param filename
	 *            A path to an XML file in Ultimate's toolchain format.
	 * @throws SAXException
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 */
	IToolchainData<T> createToolchainData(String filename) throws FileNotFoundException, JAXBException, SAXException;

	/**
	 * Create an empty toolchain data instance.
	 */
	IToolchainData<T> createToolchainData();

	/**
	 * Request an {@link IToolchain} instance from the core in order to start a new toolchain.
	 *
	 * Don't forget to release the toolchain after use.
	 *
	 * @return An {@link IToolchain} instance that can be initialized and started.
	 */
	IToolchain<T> requestToolchain();

	/**
	 * Release a previously requested {@link IToolchain} instance to invalidate all resources.
	 *
	 * @param toolchain
	 *            The toolchain that should be released.
	 */
	void releaseToolchain(IToolchain<T> toolchain);

	/**
	 * ICore will try to save all settings different from the default settings to the given path. An existing file will
	 * be overwritten.
	 *
	 * @param absolutePath
	 *            An absolute path to a (possibly existing) .epf file.
	 */
	void savePreferences(String absolutePath);

	/**
	 * ICore will try to load new settings from the given path.
	 *
	 * @param absolutePath
	 *            An absolute path to a .epf settings file compatible with Ultimate's settings.
	 */
	void loadPreferences(String absolutePath);

	/**
	 * Reset all preferences to their default values.
	 */
	void resetPreferences();

	/**
	 * Get an instance of every {@link IUltimatePlugin} that is known to the Core (this will load every UltimatePlugin).
	 */
	IUltimatePlugin[] getRegisteredUltimatePlugins();

	/**
	 * Get the name of every registered {@link IUltimatePlugin}. This will allow you to prepare for lazy loading of
	 * plugins.
	 */
	String[] getRegisteredUltimatePluginIDs();

	/**
	 * Get the core logging service. This service can be different from toolchain logging services because multiple
	 * toolchains can run in parallel.
	 */
	ILoggingService getCoreLoggingService();

	/**
	 * Get a preference provider for the specified plugin. You should use this method to retrieve preferences for the
	 * core or the currently active controller. For other plugins you should use the methods of the
	 * {@link IUltimateServiceProvider} provided by the toolchain, because multiple toolchains can run in parallel with
	 * different preferences.
	 */
	IPreferenceProvider getPreferenceProvider(String pluginId);

	/**
	 *
	 * @return A string that describes the current version of Ultimate in the form major.minor.revision-githash[-m],
	 *         e.g., 0.1.20-dc65081-m. The "-m" signals that the working copy from which the binary was build contained
	 *         local changes.
	 */
	String getUltimateVersionString();
}
