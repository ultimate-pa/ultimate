/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ReqParser plug-in.
 *
 * The ULTIMATE ReqParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ReqParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReqParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReqParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReqParer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.reqparser;

import java.util.Arrays;
import java.util.Collection;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IFailedAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

/**
 * Utility class that helps with reporting results
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ReqParserResultUtil {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private boolean mIsAborted;

	public ReqParserResultUtil(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mIsAborted = false;
	}

	@SafeVarargs
	public final <T extends PatternType> void mergedRequirements(final T... reqIds) {
		assert reqIds != null && reqIds.length > 1;
		mergedRequirements(Arrays.asList(reqIds));
	}

	public void mergedRequirements(final Collection<? extends PatternType> reqIds) {
		assert reqIds != null && reqIds.size() > 1;
		final String reqIdStr = reqIds.stream().map(a -> a.getId()).collect(Collectors.joining(", "));
		final MergedRequirementsResult result = new MergedRequirementsResult(reqIdStr);
		mLogger.warn(result.getLongDescription());
		report(result);
	}

	public void unsupportedSyntaxError(final ILocation location, final String description) {
		errorAndAbort(location + ": " + description,
				new UnsupportedSyntaxResult<>(Activator.PLUGIN_ID, location, description));
	}

	public void unexpectedParserFailure(final String filename) {
		errorAndAbort(new UnexpectedRequirementsParserFailureResult(filename));
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

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private static final class UnexpectedRequirementsParserFailureResult extends AbstractResult
			implements IFailedAnalysisResult {

		private final String mMessage;

		public UnexpectedRequirementsParserFailureResult(final String filename) {
			super(Activator.PLUGIN_ID);
			mMessage = "The parser failed on some requirements from " + filename;
		}

		@Override
		public String getShortDescription() {
			return mMessage;
		}

		@Override
		public String getLongDescription() {
			return mMessage;
		}
	}

	/**
	 * Report that states which requirements have been merged.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class MergedRequirementsResult extends GenericResult {

		/**
		 * @param reqIds
		 *            The Ids of the requirements that have been merged
		 */
		public MergedRequirementsResult(final String reqIds) {
			super(Activator.PLUGIN_ID, "Merged " + reqIds,
					"The following requirements have been merged because they are equivalent: " + reqIds,
					Severity.WARNING);
		}
	}
}
