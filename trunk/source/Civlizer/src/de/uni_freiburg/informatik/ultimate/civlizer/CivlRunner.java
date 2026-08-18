/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.Scanner;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.civlizer.results.CivlFailureResult;
import de.uni_freiburg.informatik.ultimate.civlizer.results.CivlSuccessResult;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class CivlRunner {
	private static final Pattern SUMMARY_LINE_REGEX =
			Pattern.compile("Boogie program verifier finished with (\\d+) verified, (\\d+) errors");

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final Path mWorkingDirectory;
	private final String mCivlCommand;
	private final int mTimeout;

	public CivlRunner(final IUltimateServiceProvider services, final Path workingDirectory, final String civlCommand,
			final int timeout) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());

		mWorkingDirectory = workingDirectory;
		mCivlCommand = civlCommand;
		mTimeout = timeout;
	}

	public IResult runOnFile(final File inputFile) throws IOException {
		final String[] cmdArray = { mCivlCommand, inputFile.toPath().toAbsolutePath().toString() };
		try (final MonitoredProcess civlProcess =
				MonitoredProcess.exec(cmdArray, mWorkingDirectory.toAbsolutePath().toString(), null, mServices)) {
			final String error = convertStreamToString(civlProcess.getErrorStream());
			final StringBuilder output = new StringBuilder();

			mLogger.info("Waiting for %ds for Civl...", mTimeout);
			final MonitoredProcessState civlState = civlProcess.impatientWaitUntilTime(mTimeout * 1000L);
			mLogger.info("Return code was " + civlState.getReturnCode());

			Integer errorNum = null;
			String summaryLine = null;
			try (final var outScanner = new Scanner(civlProcess.getInputStream())) {
				while (outScanner.hasNextLine()) {
					final String line = outScanner.nextLine();

					final var matcher = SUMMARY_LINE_REGEX.matcher(line);
					if (errorNum == null && matcher.matches()) {
						errorNum = Integer.parseInt(matcher.group(2));
						summaryLine = line;
					}

					output.append(line);
					output.append('\n');
				}
			}

			if (errorNum == null) {
				mLogger.warn("Civl output:\n%s", output);
				mLogger.warn("Civl errors:\n%s", error);
				throw new IllegalStateException("Could not parse verification result from Civl output");
			}

			if (errorNum.intValue() == 0) {
				return new CivlSuccessResult(summaryLine);
			}

			return new CivlFailureResult(summaryLine, output.toString(), error);
		}
	}

	private static String convertStreamToString(final InputStream stream) {
		try (Scanner s = new Scanner(stream).useDelimiter("\\A")) {
			return s.hasNext() ? s.next() : "";
		}
	}
}
