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

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class CivlRunner {
	// TODO make a setting
	private static final int TIMEOUT_IN_SECONDS = 30;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final Path mWorkingDirectory;
	private final String mCivlCommand;

	public CivlRunner(final IUltimateServiceProvider services, final Path workingDirectory, final String civlCommand) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());

		mWorkingDirectory = workingDirectory;
		mCivlCommand = civlCommand;
	}

	public void runOnFile(final File inputFile) throws IOException {
		final String[] cmdArray = { mCivlCommand, inputFile.toPath().toAbsolutePath().toString() };
		try (final MonitoredProcess civlProcess =
				MonitoredProcess.exec(cmdArray, mWorkingDirectory.toAbsolutePath().toString(), null, mServices)) {
			final String error = convertStreamToString(civlProcess.getErrorStream());
			final String output = convertStreamToString(civlProcess.getInputStream());

			mLogger.info("Waiting for %ds for Civl...", TIMEOUT_IN_SECONDS);
			final MonitoredProcessState civlState = civlProcess.impatientWaitUntilTime(TIMEOUT_IN_SECONDS * 1000L);
			mLogger.info("Return code was " + civlState.getReturnCode());

			mLogger.warn("Civl output:\n%s", output);
			mLogger.warn("Civl errors:\n%s", error);
		}
	}

	private static String convertStreamToString(final InputStream stream) {
		try (Scanner s = new Scanner(stream).useDelimiter("\\A")) {
			return s.hasNext() ? s.next() : "";
		}
	}
}
