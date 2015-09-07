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
package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.CommandLineParser;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;

/**
 * This interface describes the object that is passed to
 * {@link IController#init(ICore, ILoggingService)}.
 * 
 * {@link IController} should use at least {@link #requestToolchain()} and
 * {@link #releaseToolchain(IToolchain)} to receive {@link IToolchain} instances
 * through which Ultimate is actually controlled.
 * 
 * @author dietsch
 * 
 */
public interface ICore {

	/**
	 * Don't forget to release the toolchain after use.
	 * 
	 * @return An {@link IToolchain} instance that can be initialized and
	 *         started.
	 */
	IToolchain requestToolchain();

	/**
	 * Release a previously requested {@link IToolchain} instance to invalidate
	 * all resources.
	 * 
	 * @param toolchain
	 */
	void releaseToolchain(IToolchain toolchain);

	/**
	 * ICore will try to save all settings different from the default settings
	 * to the given path. An existing file will be overwritten.
	 * 
	 * @return An absolute path to a (possibly existing) .epf file
	 */
	void savePreferences(String absolutePath);

	/**
	 * ICore will try to load new settings from the given path.
	 * 
	 * @return An absolute path to a .epf settings file compatible with
	 *         Ultimate's settings.
	 */
	void loadPreferences(String absolutePath);

	/**
	 * Reset all preferences to their default values.
	 */
	void resetPreferences();

	/**
	 * Get an instance of every {@link IUltimatePlugin} that is known to the
	 * Core (this will load every UltimatePlugin).
	 * 
	 * @return
	 */
	IUltimatePlugin[] getRegisteredUltimatePlugins();

	/**
	 * Get the name of every registered {@link IUltimatePlugin}. This will allow
	 * you to prepare for lazy loading of plugins.
	 * 
	 * @return
	 */
	String[] getRegisteredUltimatePluginIDs();

	/**
	 * 
	 * @return
	 */
	CommandLineParser getCommandLineArguments();

}
