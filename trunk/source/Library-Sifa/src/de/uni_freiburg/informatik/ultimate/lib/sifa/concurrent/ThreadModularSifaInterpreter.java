/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.reporting.SifaResultPrinter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSetup;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ThreadInvariants;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ThreadAnalyzer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.fixpoint.OuterInterferenceFixpoint;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public class ThreadModularSifaInterpreter implements ISifaInterpreter {
	private final ILogger mLogger;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Collection<IcfgLocation> mRequestedLocationsOfInterest;
	private final ConcurrentSymbolicTools mConcurrentTools;
	private final OuterInterferenceFixpoint mOuterFixpoint;
	private final SifaResultPrinter mResultPrinter;
	private final ThreadModularProofChecker mProofChecker;

	public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final ConcurrentSymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mIcfg = icfg;
		mRequestedLocationsOfInterest = locationsOfInterest == null ? Set.of() : Set.copyOf(locationsOfInterest);
		mConcurrentTools = tools;

		final var setup = ThreadModularSetup.initialize(services, icfg, baseDomain, mConcurrentTools);
		setup.postcondition().setStats(stats);
		mProofChecker = setup.proofChecker();
		final ThreadAnalyzer threadAnalysis = new ThreadAnalyzer(logger, timer, stats, mConcurrentTools, icfg,
				mRequestedLocationsOfInterest, setup.domain(), fluid, loopSumFactory, callSumFactory, setup.threadIds(),
				setup.joinedThreads());
		mOuterFixpoint = new OuterInterferenceFixpoint(logger, mConcurrentTools, setup.domain(),
				setup.interferenceFactory(), setup.publication(),
				mConcurrentTools.getSettings().outerWideningThreshold(), threadAnalysis);
		mResultPrinter = mConcurrentTools.getSettings().resultPrint()
				? new SifaResultPrinter(logger, setup.abstractLocationIds(),
						mConcurrentTools.getThreadActivityPreanalysis())
				: null;
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		final ThreadInvariants invariants = mOuterFixpoint.compute();
		if (mResultPrinter != null) {
			mResultPrinter.printResults(invariants.locationInvariants(), mIcfg);
		}
		if (mProofChecker != null) {
			mProofChecker.checkAllOrThrow(invariants, mLogger);
		}
		return requestedLocationPredicates(invariants.locationInvariants());
	}

	private Map<IcfgLocation, IPredicate> requestedLocationPredicates(
			final Map<IcfgLocation, IPredicate> locationInvariants) {
		final Map<IcfgLocation, IPredicate> result = new LinkedHashMap<>();
		for (final IcfgLocation location : mRequestedLocationsOfInterest) {
			result.put(location, locationInvariants.getOrDefault(location, mConcurrentTools.bottom()));
		}
		return result;
	}
}
