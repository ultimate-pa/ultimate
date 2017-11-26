/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtParser plug-in.
 *
 * The ULTIMATE SmtParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Use external tool to do a syntax check.
 *
 * @author Matthias Heizmann
 */
public class SyntaxChecker implements IAnalysis {
	private static final int SYNTAX_CHECKER_TIMEOUT_MS = 20 * 1000;
	protected String[] mFileTypes;
	protected ILogger mLogger;
	protected List<String> mFileNames;
	protected Unit mPreludeUnit;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;

	private FilenameExtractionObserver mFilenameExtractionObserver;

	@Override
	public ModelType getOutputDefinition() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.SOURCE;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		// not needed
	}

	@Override
	public List<IObserver> getObservers() {
		return Arrays.asList(new IObserver[] { mFilenameExtractionObserver });
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
		mFilenameExtractionObserver = new FilenameExtractionObserver(mLogger);
	}

	@Override
	public void finish() {
		try {
			doSyntaxCheck();
		} catch (final IOException e) {
			throw new ToolchainCanceledException(e.getMessage(), SyntaxChecker.class, "Syntax Checking");
		}
	}

	private void doSyntaxCheck() throws IOException {
		final String toolCommandError = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getString(PreferenceInitializer.LABEL_SyntaxErrorCommand);
		final String filename = mFilenameExtractionObserver.getFilename();

		final boolean removeFilename = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.LABEL_RemoveFilename);

		final String outputError = callSytaxCheckerAndReturnStderrOutput(toolCommandError, filename);
		if (outputError == null) {
			// everything fine, do nothing
		} else {
			final String longMessage = generateLongDescription(toolCommandError, outputError, filename, removeFilename);
			final ILocation loc = new DummyLocation();
			final SyntaxErrorResult res = new SyntaxErrorResult(Activator.PLUGIN_ID, loc, longMessage);
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
			mServices.getProgressMonitorService().cancelToolchain();
		}

		final boolean doSyntaxWarningCheck = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.LABEL_DoSyntaxWarningCheck);
		if (doSyntaxWarningCheck) {
			final String toolCommandWarnings = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getString(PreferenceInitializer.LABEL_SyntaxErrorCommand);
			final String outputWarnings;
			if (Objects.equals(toolCommandError, toolCommandWarnings)) {
				outputWarnings = outputError;
			} else {
				outputWarnings = callSytaxCheckerAndReturnStderrOutput(toolCommandWarnings, filename);
			}
			if (outputWarnings == null) {
				// everything fine, do nothing
			} else {
				final String longMessage =
						generateLongDescription(toolCommandError, outputWarnings, filename, removeFilename);
				final String shortDescription = "Syntax checker warnings";
				final Severity severity = Severity.WARNING;
				final GenericResult res =
						new GenericResult(Activator.PLUGIN_ID, shortDescription, longMessage, severity);
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
			}
		}
	}

	private static String generateLongDescription(final String toolCommand, final String outputError,
			final String filename, final boolean replaceFilename) {
		final String toolOutput;
		if (replaceFilename) {
			toolOutput = outputError.replaceAll(filename, "");
		} else {
			toolOutput = outputError;
		}
		return "Syntax check with command \"" + toolCommand + "\" returned the following output. "
				+ System.lineSeparator() + toolOutput;
	}

	private String callSytaxCheckerAndReturnStderrOutput(final String toolCommand, final String filename)
			throws IOException {
		final String syntaxCheckerCommand = toolCommand + " " + filename;
		final MonitoredProcess mProcess =
				MonitoredProcess.exec(syntaxCheckerCommand, null, mServices, mStorage, mLogger);

		if (mProcess == null) {
			final String errorMsg = " Could not create process, terminating... ";
			mLogger.fatal(errorMsg);
			throw new IllegalStateException(errorMsg);
		}
		// Let all processes terminate when the toolchain terminates
		mProcess.setTerminationAfterToolchainTimeout(SYNTAX_CHECKER_TIMEOUT_MS);

		final String stderr = convert(mProcess.getErrorStream());
		return stderr;
	}

	private static String convert(final InputStream is) throws IOException {
		final InputStreamReader isr = new InputStreamReader(is);
		final BufferedReader br = new BufferedReader(isr);
		String line = br.readLine();
		if (line == null) {
			return null;
		}
		final StringBuilder sb = new StringBuilder();
		sb.append(line);
		line = br.readLine();
		while (line != null) {
			sb.append(System.lineSeparator());
			sb.append(line);
			line = br.readLine();
		}
		return sb.toString();
	}

	@Override
	public String getPluginName() {
		return "SyntaxChecker";
	}

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	private final class DummyLocation extends DefaultLocation {

		private static final long serialVersionUID = 1L;

		public DummyLocation() {
			super(mFilenameExtractionObserver.getFilename(), -1, 0, 0, 0);
		}
	}
}
