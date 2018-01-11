/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.externaltools;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.deltadebugger.Activator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.preferences.DeltaDebuggerPreferences;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class ExternalTool implements IExternalTool {

	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;

	public ExternalTool(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mServices = Objects.requireNonNull(services);
		mStorage = Objects.requireNonNull(storage);
		mLogger = services.getLoggingService().getControllerLogger();
	}

	@Override
	public ExternalToolResult runExternalTool(final File inputFile) {
		if (!checkAndSetupTool()) {
			return ExternalToolResult.INVALID;
		}

		final String[] cmd = getCommandline(inputFile.getAbsolutePath());
		final String workingDir = getWorkingDir();
		final String exitCommand = getExitCommand();

		mLogger.info(String.format("Preparing to run command %s in directory %s with exit command %s",
				Arrays.toString(cmd), workingDir, exitCommand));
		MonitoredProcess extProcess;
		try {
			extProcess = MonitoredProcess.exec(cmd, workingDir, exitCommand, mServices, mStorage);
		} catch (final IOException e) {
			mLogger.fatal("External tool could not be run. Reason:", e);
			return ExternalToolResult.INVALID;
		}
		final BufferedInputStream errorStream = new BufferedInputStream(extProcess.getErrorStream());
		final BufferedInputStream outputStream = new BufferedInputStream(extProcess.getInputStream());
		final String error = CoreUtil.convertStreamToString(errorStream);
		final String output = CoreUtil.convertStreamToString(outputStream);

		final long hardTimeout = getHardTimeout();
		mLogger.info("Waiting for " + hardTimeout + "ms for external tool...");
		final MonitoredProcessState extProcState = extProcess.impatientWaitUntilTime(hardTimeout);
		final int returnCode = extProcState.getReturnCode();
		mLogger.info("Return code of external tool was " + extProcState.getReturnCode());

		final ExternalToolResult result = interpretResult(output, error, returnCode, extProcState.isKilled());
		return result;
	}

	protected abstract ExternalToolResult interpretResult(final String output, final String error, final int returnCode,
			final boolean killed);

	protected abstract String getExitCommand();

	protected abstract String getWorkingDir();

	protected abstract String[] getCommandline(String inputFilePath);

	protected abstract boolean checkAndSetupTool();

	protected long getHardTimeout() {
		final IPreferenceProvider prefProvider = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		return prefProvider.getLong(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_TIMEOUT);
	}

}
