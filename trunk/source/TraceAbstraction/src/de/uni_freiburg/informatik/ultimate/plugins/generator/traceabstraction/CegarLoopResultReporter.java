/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;
import java.util.function.BiConsumer;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.DataRaceFoundResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TestGenerationResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UserSpecifiedLimitReachedResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgAngelicProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.TestGenerationMode;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class CegarLoopResultReporter<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final BiConsumer<IcfgLocation, IResult> mReportFunction;
	private final String mPluginId;
	private final String mPluginName;
	protected final TAPreferences mPref;
	protected TestGenerationMode mTestGeneration;

	/**
	 * Constructor s.t. the {@link CegarLoopResultReporter} reports all created results immediately to
	 * {@link IResultService}.
	 */
	public CegarLoopResultReporter(final IUltimateServiceProvider services, final ILogger logger, final String pluginId,
			final String pluginName) {
		mServices = services;

		mLogger = logger;
		mPluginId = pluginId;
		mPluginName = pluginName;
		mReportFunction = (errorLoc, result) -> this.reportResult(result);
		mPref = new TAPreferences(mServices);
		mTestGeneration = mPref.getTestGeneration();
	}

	/**
	 * Constructor with reportFunction that allows you to consume the created results without them being recorded. you
	 * can then filter them and manually report them via {@link #reportResult(IResult)}.
	 */
	public CegarLoopResultReporter(final IUltimateServiceProvider services, final ILogger logger, final String pluginId,
			final String pluginName, final BiConsumer<IcfgLocation, IResult> reportFunction) {
		mServices = services;
		mLogger = logger;
		mPluginId = pluginId;
		mPluginName = pluginName;
		mReportFunction = reportFunction;
		mPref = new TAPreferences(mServices);
		mTestGeneration = mPref.getTestGeneration();
	}

	public void reportCegarLoopResult(final CegarLoopResult<L> clres) {
		for (final Entry<IcfgLocation, CegarLoopLocalResult<L>> entry : clres.getResults().entrySet()) {
			final CegarLoopLocalResult<L> localResult = entry.getValue();
			final IcfgLocation errorLoc = entry.getKey();
			switch (localResult.getResult()) {
			case SAFE:
				reportPositiveResult(errorLoc);
				break;
			case UNSAFE:
				reportCounterexampleResult(errorLoc, localResult.getProgramExecution());
				break;
			case TIMEOUT:
			case USER_LIMIT_ITERATIONS:
			case USER_LIMIT_PATH_PROGRAM:
			case USER_LIMIT_TIME:
			case USER_LIMIT_TRACEHISTOGRAM:
				reportLimitResult(errorLoc, localResult);
				break;
			case UNKNOWN:
				final IProgramExecution<L, Term> pe = localResult.getProgramExecution();
				reportUnproveableResult(errorLoc, pe, localResult.getUnprovabilityReasons());
				break;
			case TEST_GENERATION:
				// reportCounterexampleResult(errorLoc, localResult.getProgramExecution());
				reportTestGenerationResult(errorLoc, localResult.getProgramExecution());
				break;
			default:
				throw new UnsupportedOperationException("Unknown result type " + localResult.getResult());
			}
		}
	}

	public void reportAllSafeResultIfNecessary(final CegarLoopResult<L> clres, final int numberOfErrorLocs) {
		reportAllSafeResultIfNecessary(Collections.singletonList(clres), numberOfErrorLocs);
	}

	public void reportAllSafeResultIfNecessary(final Collection<CegarLoopResult<L>> clres,
			final int numberOfErrorLocs) {
		if (clres.stream().allMatch(a -> a.resultStream().allMatch(r -> r == Result.SAFE))) {
			final AllSpecificationsHoldResult result =
					AllSpecificationsHoldResult.createAllSpecificationsHoldResult(mPluginName, numberOfErrorLocs);
			reportResult(result);
		}
	}

	public void reportResult(final IResult res) {
		mServices.getResultService().reportResult(mPluginId, res);
	}

	private void reportPositiveResult(final IcfgLocation errorLoc) {
		final PositiveResult<IIcfgElement> pResult =
				new PositiveResult<>(mPluginName, errorLoc, mServices.getBacktranslationService());
		mReportFunction.accept(errorLoc, pResult);
	}

	private void reportTestGenerationResult(final IcfgLocation errorLoc, final IProgramExecution<L, Term> pe) {
		final List<UnprovabilityReason> upreasons = UnprovabilityReason.getUnprovabilityReasons(pe);
		if (!upreasons.isEmpty()) {
			final IResult cexResult = new TestGenerationResult(mPluginName, true);
			mReportFunction.accept(errorLoc, cexResult);
			return;
		}
		final IResult cexResult = new TestGenerationResult(mPluginName, false);
		mReportFunction.accept(errorLoc, cexResult);
	}

	private void reportCounterexampleResult(final IcfgLocation errorLoc, final IProgramExecution<L, Term> pe) {

		final List<UnprovabilityReason> upreasons = UnprovabilityReason.getUnprovabilityReasons(pe);
		if (!upreasons.isEmpty()) {
			reportUnproveableResult(errorLoc, pe, upreasons);
			return;
		}
		assert pe == null || errorLoc == getErrorPP(pe);
		if (isAngelicallySafe(pe)) {
			mLogger.info("Ignoring angelically safe counterexample for %s", errorLoc);
			return;
		}
		final Check check = Check.getAnnotation(errorLoc);
		IResult cexResult;
		if (check != null && check.getSpec().contains(Spec.DATA_RACE)) {
			cexResult = new DataRaceFoundResult<>(errorLoc, mPluginName, mServices.getBacktranslationService(), pe);
		} else {
			cexResult = new CounterExampleResult<>(errorLoc, mPluginName, mServices.getBacktranslationService(), pe);
		}

		mReportFunction.accept(errorLoc, cexResult);
	}

	private void reportLimitResult(final IcfgLocation errorLoc, final CegarLoopLocalResult<L> result) {
		final IResult res = constructLimitResult(mServices, result, errorLoc);
		mReportFunction.accept(errorLoc, res);
	}

	private void reportUnproveableResult(final IcfgLocation errorLoc, final IProgramExecution<L, Term> pe,
			final List<UnprovabilityReason> unprovabilityReasons) {
		assert pe == null || errorLoc == getErrorPP(pe);
		final IResult res = new UnprovableResult<>(mPluginName, errorLoc, mServices.getBacktranslationService(), pe,
				unprovabilityReasons);
		mReportFunction.accept(errorLoc, res);
	}

	private IResult constructLimitResult(final IUltimateServiceProvider services, final CegarLoopLocalResult<L> result,
			final IcfgLocation errorIpp) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Unable to prove that ");
		sb.append(Check.getAnnotation(errorIpp).getPositiveMessage());
		if (errorIpp instanceof BoogieIcfgLocation) {
			final ILocation origin = ((BoogieIcfgLocation) errorIpp).getBoogieASTNode().getLocation();
			sb.append(" (line ").append(origin.getStartLine()).append(").");
		}

		if (result.getRunningTaskStackProvider() != null) {
			sb.append(" Cancelled ").append(result.getRunningTaskStackProvider().printRunningTaskMessage());
		}

		final Result resultCategory = result.getResult();
		final IResult res;
		if (resultCategory == Result.TIMEOUT) {
			res = new TimeoutResultAtElement<>(errorIpp, mPluginName, services.getBacktranslationService(),
					sb.toString());
		} else {
			res = new UserSpecifiedLimitReachedResultAtElement<IElement>(resultCategory.toString(), errorIpp,
					mPluginName, services.getBacktranslationService(), result.getProgramExecution(), sb.toString());
		}
		return res;
	}

	private boolean isAngelicallySafe(final IProgramExecution<L, Term> pe) {
		if (pe instanceof IcfgAngelicProgramExecution) {
			return !((IcfgAngelicProgramExecution<L>) pe).getAngelicStatus();
		}
		return false;
	}

	private IcfgLocation getErrorPP(final IProgramExecution<L, Term> pe) {
		final int lastPosition = pe.getLength() - 1;
		final IIcfgTransition<?> last = pe.getTraceElement(lastPosition).getTraceElement();
		return last.getTarget();
	}

}