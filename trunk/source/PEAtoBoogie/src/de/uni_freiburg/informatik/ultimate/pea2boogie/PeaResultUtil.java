/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.IResultWithCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator.InvariantInfeasibleException;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheck;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckFailResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckSuccessResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementInconsistentErrorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementTransformationErrorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementTypeErrorResult;

/**
 * Utility class that helps with reporting results.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PeaResultUtil {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private boolean mIsAborted;
	private final Set<String> mExprWithTypeErrors;

	public PeaResultUtil(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mIsAborted = false;
		mExprWithTypeErrors = new HashSet<>();
	}

	public boolean isAlreadyAborted() {
		return mIsAborted;
	}

	public void transformationError(final PatternType req, final String reason) {
		assert req != null;
		final IResult result = new RequirementTransformationErrorResult(req.getId(), reason);
		mLogger.warn(result.getLongDescription());
		report(result);
	}

	public void syntaxError(final ILocation location, final String description) {
		errorAndAbort(location, description, new SyntaxErrorResult(Activator.PLUGIN_ID, location, description));
	}

	public void typeError(final PatternType req, final String description) {
		errorAndAbort(new RequirementTypeErrorResult(req.getId(), description));
	}

	public void typeError(final String description, final Expression expr) {
		if (mExprWithTypeErrors.add(expr.toString())) {
			errorAndAbort(new RequirementTypeErrorResult(expr.getLoc().getStartLine(),
					BoogiePrettyPrinter.print(expr) + " :" + description));
		}
	}

	public void intrinsicRtConsistencySuccess(final IElement element) {
		final String plugin = Activator.PLUGIN_ID;
		final IBacktranslationService translatorSequence = mServices.getBacktranslationService();
		report(new ReqCheckSuccessResult<>(element, plugin, translatorSequence));
	}

	public void infeasibleInvariant(final InvariantInfeasibleException ex) {
		errorAndAbort(new RequirementInconsistentErrorResult(ex));
	}

	public IResult convertTraceAbstractionResult(final IResult result) {
		final AbstractResultAtElement<?> oldRes;
		final ReqCheck reqCheck;
		boolean isPositive;
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			oldRes = (AbstractResultAtElement<?>) result;
			reqCheck = (ReqCheck) ((IResultWithCheck) result).getCheckedSpecification();
			isPositive = false;
		} else if (result instanceof PositiveResult<?>) {
			oldRes = (AbstractResultAtElement<?>) result;
			reqCheck = (ReqCheck) ((IResultWithCheck) result).getCheckedSpecification();
			isPositive = true;
		} else if (result instanceof AllSpecificationsHoldResult) {
			// makes no sense in our context, suppress it
			return null;
		} else {
			return result;
		}

		if (reqCheck.getSpec() == null || reqCheck.getSpec().isEmpty()) {
			mLogger.error("Ignoring illegal empty check");
			return result;
		} else if (reqCheck.getSpec().size() == 1) {
			final Spec spec = reqCheck.getSpec().iterator().next();
			// a counterexample for consistency and vacuity means that the requirements are consistent or non-vacuous
			switch (spec) {
			case CONSISTENCY:
			case VACUOUS:
				// fall-through is deliberately
				isPositive = !isPositive;
			case RTINCONSISTENT:
				final IElement element = oldRes.getElement();
				final String plugin = oldRes.getPlugin();
				final IBacktranslationService translatorSequence = oldRes.getCurrentBacktranslation();
				return isPositive ? new ReqCheckSuccessResult<>(element, plugin, translatorSequence)
						: new ReqCheckFailResult<>(element, plugin, translatorSequence);
			default:
				mLogger.error("Ignoring illegal check type " + spec);
				return result;
			}
		} else {
			mLogger.error("Ignoring multi-check");
			return result;
		}
	}

	private void errorAndAbort(final IResult result) {
		mLogger.error(result.getLongDescription());
		report(result);
		mServices.getProgressMonitorService().cancelToolchain();
		mIsAborted = true;
	}

	private void errorAndAbort(final ILocation location, final String description, final IResult result) {
		mLogger.error(location + ": " + description);
		report(result);
		mServices.getProgressMonitorService().cancelToolchain();
		mIsAborted = true;
	}

	private void report(final IResult result) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

}
