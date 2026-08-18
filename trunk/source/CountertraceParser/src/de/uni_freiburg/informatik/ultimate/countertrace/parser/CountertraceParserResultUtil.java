/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CountertraceParser plug-in.
 *
 * The ULTIMATE CountertraceParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CountertraceParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CountertraceParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CountertraceParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CountertraceParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.countertrace.parser;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IFailedAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Utility class that helps with reporting results for the countertrace parser.
 */
public class CountertraceParserResultUtil {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private boolean mIsAborted;

	public CountertraceParserResultUtil(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mIsAborted = false;
	}

	public void unsupportedSyntaxError(final ILocation location, final String description) {
		errorAndAbort(location + ": " + description,
				new UnsupportedSyntaxResult<>(Activator.PLUGIN_ID, location, description));
	}

	public void unexpectedParserFailure(final String filename, final String message) {
		errorAndAbort(new UnexpectedCountertraceParserFailureResult(filename, message));
	}

	public boolean isAlreadyAborted() {
		return mIsAborted;
	}

	private void errorAndAbort(final IResult result) {
		errorAndAbort(result.getShortDescription(), result);
	}

	private void errorAndAbort(final String message, final IResult result) {
		mLogger.error(message);
		report(result);
		mServices.getProgressMonitorService().cancelToolchain();
		mIsAborted = true;
	}

	private void report(final IResult result) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

	private static final class UnexpectedCountertraceParserFailureResult extends AbstractResult
			implements IFailedAnalysisResult {

		private final String mMessage;
		private final String mLongMessage;

		public UnexpectedCountertraceParserFailureResult(final String filename, final String message) {
			super(Activator.PLUGIN_ID);
			mMessage = String.format("The countertrace parser failed on file %s", filename);
			mLongMessage = message;
		}

		@Override
		public String getShortDescription() {
			return mMessage;
		}

		@Override
		public String getLongDescription() {
			return mLongMessage;
		}
	}
}
