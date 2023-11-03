/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE JUnit Helper Library.
 *
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.mocks;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TimeoutHandler;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateMocks {

	private UltimateMocks() {
		// do not instantiate utility class
	}

	public static IUltimateServiceProvider createUltimateServiceProviderMock() {
		return createUltimateServiceProviderMock(LogLevel.DEBUG);
	}

	public static IUltimateServiceProvider createUltimateServiceProviderMock(final LogLevel defaultLogLevel) {
		return new UltimateServiceProviderMock(defaultLogLevel);
	}

	public static Script createZ3Script() {
		return createZ3Script(LogLevel.DEBUG);
	}

	public static Script createZ3Script(final LogLevel defaultLogLevel) {
		return createSolver("z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in", defaultLogLevel);
	}

	public static Script createCVC4Script(final LogLevel defaultLogLevel) {
		// tlimit is given in milliseconds
		return createSolver("cvc4 --incremental --print-success --lang smt --tlimit-per=12000", defaultLogLevel);
	}

	/**
	 * If the solverCommand is of the form `INTERNAL_SMTINTERPOL:n` where n is the
	 * decimal representation of a long value. We utilize the internal SMTINterpol
	 * with a timeout of n milliseconds.
	 */
	public static Script createSolver(final String solverCommand, final LogLevel defaultLogLevel) {
		final IUltimateServiceProvider services = createUltimateServiceProviderMock(defaultLogLevel);
		final ILogger logger = services.getLoggingService().getLogger(UltimateMocks.class);
		if (solverCommand.startsWith("INTERNAL_SMTINTERPOL:")) {
			final String timeoutMillisAsString = solverCommand.substring(21);
			final long timeoutMillisAsLong = Long.parseLong(timeoutMillisAsString);
			final LogProxy loggerWrapper = new SmtInterpolLogProxyWrapper(logger);
			final TimeoutHandler timeoutHandler = new TimeoutHandler(null);
			timeoutHandler.setTimeout(timeoutMillisAsLong);
			return new SMTInterpol(loggerWrapper, timeoutHandler);
		} else {
			try {
				return new Scriptor(solverCommand, logger, services, "SMT solver", null);
			} catch (final IOException e) {
				throw new RuntimeException(e);
			}
		}
	}
}
