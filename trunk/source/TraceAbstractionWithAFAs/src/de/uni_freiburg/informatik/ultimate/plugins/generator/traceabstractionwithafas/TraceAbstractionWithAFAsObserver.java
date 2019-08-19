/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionWithAFAs plug-in.
 *
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionWithAFAs plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionWithAFAs plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionWithAFAs plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionWithAFAsObserver extends BaseObserver {

	/**
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node exactly the initial nodes of procedures.
	 */
	private final IElement mGraphroot = null;

	private final IUltimateServiceProvider mServices;

	private final ILogger mLogger;

	public TraceAbstractionWithAFAsObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {

		final BoogieIcfgContainer rootAnnot = (BoogieIcfgContainer) root;
		final TAPreferences taPrefs = new TAPreferences(mServices);
		final CfgSmtToolkit csToolkit = rootAnnot.getCfgSmtToolkit();
		final PredicateFactory predicateFactory = new PredicateFactory(mServices, csToolkit.getManagedScript(),
				csToolkit.getSymbolTable());
		final TraceAbstractionBenchmarks taBenchmarks = new TraceAbstractionBenchmarks(rootAnnot);

		final Map<String, Set<BoogieIcfgLocation>> proc2errNodes = rootAnnot.getProcedureErrorNodes();
		final Collection<BoogieIcfgLocation> errNodesOfAllProc = new ArrayList<>();
		for (final Collection<BoogieIcfgLocation> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		final TAwAFAsCegarLoop<IcfgEdge> cegarLoop =
				new TAwAFAsCegarLoop<>(TraceAbstractionStarter.AllErrorsAtOnceDebugIdentifier.INSTANCE, rootAnnot,
						csToolkit, predicateFactory, taBenchmarks, taPrefs, errNodesOfAllProc, taPrefs.interpolation(),
						taPrefs.computeHoareAnnotation(), mServices);

		final Result result = cegarLoop.iterate();

		cegarLoop.finish();

		final TraceAbstractionBenchmarks taBenchmark = new TraceAbstractionBenchmarks(rootAnnot);
		final CegarLoopStatisticsGenerator cegarLoopBenchmarkGenerator = cegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
		taBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
		reportBenchmark(taBenchmark);

		if (result == Result.SAFE) {
			reportPositiveResults(errNodesOfAllProc);
		} else if (result == Result.UNSAFE) {
			reportCounterexampleResult(cegarLoop.getRcfgProgramExecution());
		} else {
			final String shortDescription = "Unable to decide if program is safe!";
			final String longDescription = "Unable to decide if program is safe!";
			final GenericResult genResult =
					new GenericResult(Activator.PLUGIN_NAME, shortDescription, longDescription, Severity.INFO);
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, genResult);
		}
		return false;
	}

	private <T> void reportBenchmark(final ICsvProviderProvider<T> benchmark) {
		final String shortDescription = "Ultimate CodeCheck benchmark data";
		final StatisticsResult<T> res = new StatisticsResult<>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private void reportPositiveResults(final Collection<BoogieIcfgLocation> errorLocs) {
		if (!errorLocs.isEmpty()) {
			for (final BoogieIcfgLocation errorLoc : errorLocs) {
				final PositiveResult<IIcfgElement> pResult =
						new PositiveResult<>(Activator.PLUGIN_NAME, errorLoc, mServices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		final AllSpecificationsHoldResult result =
				AllSpecificationsHoldResult.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, errorLocs.size());
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe) {
		final List<UnprovabilityReason> upreasons = UnprovabilityReason.getUnprovabilityReasons(pe);
		if (!upreasons.isEmpty()) {
			reportUnproveableResult(pe, upreasons);
			return;
		}
		reportResult(new CounterExampleResult<>(getErrorPP(pe), Activator.PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe,
			final List<UnprovabilityReason> unproabilityReasons) {
		final BoogieIcfgLocation errorPP = getErrorPP(pe);
		final UnprovableResult<IIcfgElement, IIcfgTransition<IcfgLocation>, Term> uknRes = new UnprovableResult<>(
				Activator.PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	public BoogieIcfgLocation getErrorPP(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe) {
		final int lastPosition = pe.getLength() - 1;
		final IIcfgTransition<IcfgLocation> last = pe.getTraceElement(lastPosition).getTraceElement();
		final BoogieIcfgLocation errorPP = (BoogieIcfgLocation) last.getTarget();
		return errorPP;
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return mGraphroot;
	}

}
