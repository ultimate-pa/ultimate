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

package de.uni_freiburg.informatik.ultimate.core.model.services;

import java.io.Writer;

import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ILoggingService {

	/**
	 * Gets the correct logger for a particular plug-in. This method should be called by all plug-ins that extend
	 * {@link ITool} and by the Core Plugin and want to access their {@link ILogger}. Appenders are set as defaults and
	 * log levels are set using preferences. <br/>
	 * <br/>
	 * <b>Usage:</b> Most tools can use their Activator.PLUGIN_ID as argument.<br/>
	 * <br/>
	 * Not to be used for external tools or the controller plug-in.
	 *
	 * @param pluginId
	 *            is the PluginId of the plug-in to which the caller belongs.
	 * @return an initialized {@link ILogger} instance.
	 */
	ILogger getLogger(String pluginId);

	/**
	 * Gets the correct logger for a caller that does not want to be associated with a plug-in or an external tool.
	 * Appenders are set as defaults and log levels are set using preferences. <br/>
	 *
	 * @param clazz
	 *            is the {@link Class} of the calling method.
	 * @return an initialized {@link ILogger} instance.
	 */
	ILogger getLogger(Class<?> clazz);

	/**
	 * Set log level for logger requested by clazz for the duration of this toolchain.
	 *
	 * @param clazz
	 * @param level
	 */
	void setLogLevel(Class<?> clazz, LogLevel level);

	/**
	 * Set log level for logger with id <code>id</code> for the duration of this toolchain.
	 *
	 * @param clazz
	 * @param level
	 */
	void setLogLevel(String id, LogLevel level);

	/**
	 * Gets the correct logger for an asking external tool This method should be called by all external tools that want
	 * to access their {@link ILogger}. Appenders are set as defaults and log levels are set using the preferences <br/>
	 *
	 * Not to be used for plug-ins.
	 *
	 * @param id
	 *            is an identifier for the external tool to which the caller belongs.
	 * @return an initialized {@link ILogger} instance that can be used by an external tool.
	 */
	ILogger getLoggerForExternalTool(String id);

	/**
	 * Gets the correct logger for the controller plug-in. This method should be called by all controller plug-ins that
	 * want to access their {@link ILogger}. Appenders are set as defaults and log levels are set using preferences.
	 * <br/>
	 *
	 * @return ILogger for the current controller.
	 */
	ILogger getControllerLogger();

	/**
	 * Tries to convert the Ultimate logger to a backing type specified by the client.
	 *
	 * Used as a hack until SMTInterpol has a log4j-independent logging system. You should not use this!
	 *
	 * @param logger
	 *            An Ultimate logger
	 * @param backingType
	 *            The type you want to have
	 * @return An instance of the backing type you specified if you guessed right, else null.
	 */
	Object getBacking(ILogger logger, Class<?> backingType);

	void addWriter(Writer writer, String logPattern);

	void removeWriter(Writer writer);

	void reloadLoggers();

	void setCurrentControllerID(String name);

	void store(IToolchainStorage storage);
}
