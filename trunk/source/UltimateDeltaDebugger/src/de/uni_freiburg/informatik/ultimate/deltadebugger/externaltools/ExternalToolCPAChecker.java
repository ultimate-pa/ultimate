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

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
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
public class ExternalToolCPAChecker extends ExternalTool {

	private String mCpaCheckerHome;
	private final IPreferenceProvider mPrefProvider;

	public ExternalToolCPAChecker(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		super(services, storage);
		mPrefProvider = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	@Override
	protected ExternalToolResult interpretResult(final String output, final String error, final int returnCode,
			final boolean killed) {

		if (killed) {
			logOutput(output, error, returnCode, killed);
			return ExternalToolResult.TIMEOUT;
		}

		final Predicate<String> isInteresting =
				getOutputPredicate(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_CPACHECKER_OUTPUT_REGEX_INTERESTING);
		final Predicate<String> isOOM =
				getOutputPredicate(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_CPACHECKER_OUTPUT_REGEX_OOM);
		final Predicate<String> isTimeout =
				getOutputPredicate(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_CPACHECKER_OUTPUT_REGEX_TIMEOUT);
		final Predicate<String> isError =
				getOutputPredicate(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_CPACHECKER_OUTPUT_REGEX_ERROR);

		ExternalToolResult result = ExternalToolResult.UNKNOWN;

		for (final String line : output.split(CoreUtil.getPlatformLineSeparator())) {
			if (isInteresting.test(line)) {
				result = ExternalToolResult.INTERESTING;
				break;
			} else if (isOOM.test(line)) {
				result = ExternalToolResult.OOM;
				break;
			} else if (isTimeout.test(line)) {
				result = ExternalToolResult.TIMEOUT;
				break;
			} else if (isError.test(line)) {
				result = ExternalToolResult.ERROR;
				break;
			}
		}
		if (result != ExternalToolResult.INTERESTING) {
			logOutput(output, error, returnCode, killed);
		}
		return result;
	}

	private void logOutput(final String output, final String error, final int returnCode, final boolean killed) {
		mLogger.info("CPAChecker terminated with return code " + returnCode);
		if (killed) {
			mLogger.info("CPAChecker was killed due to hard timeout");
		}
		mLogger.info("STDOUT:");
		mLogger.info(output);
		mLogger.info("STDERR:");
		mLogger.info(error);
	}

	@Override
	protected String getExitCommand() {
		return null;
	}

	@Override
	protected String getWorkingDir() {
		if (mCpaCheckerHome == null) {
			mCpaCheckerHome = initWorkingDir();
		}
		return mCpaCheckerHome;
	}

	@Override
	protected String[] getCommandline(final String inputFilePath) {
		final String command = mPrefProvider.getString(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_CPACHECKER_CMD);
		final String[] args = command.split(" ");

		final List<String> cmdArgs = new ArrayList<>();

		cmdArgs.add(Paths.get(mCpaCheckerHome, args[0]).toFile().getAbsolutePath());

		for (int i = 1; i < args.length; ++i) {
			cmdArgs.add(args[i]);
		}
		cmdArgs.add("-timelimit");
		cmdArgs.add(String.valueOf(getHardTimeout() / 1000L));
		cmdArgs.add(inputFilePath);
		return cmdArgs.toArray(new String[cmdArgs.size()]);
	}

	@Override
	protected boolean checkAndSetupTool() {
		if (getWorkingDir() == null) {
			mLogger.error("CPACHECKER_HOME not set, cannot use CPACHECKER as witness verifier");
			return false;
		}
		return true;
	}

	private String initWorkingDir() {
		final String rtr = System.getenv().get("CPACHECKER_HOME");
		if (rtr == null) {
			return mPrefProvider.getString(DeltaDebuggerPreferences.LABEL_EXTERNAL_TOOL_WORKING_DIR);
		}
		return rtr;
	}

	private Predicate<String> getOutputPredicate(final String label) {
		if (label == null || label.isEmpty()) {
			return a -> false;
		}
		final String regex = mPrefProvider.getString(label);
		if (regex == null || regex.isEmpty()) {
			return a -> false;
		}
		final Pattern matcher = Pattern.compile(regex);
		return matcher.asPredicate();
	}

}
