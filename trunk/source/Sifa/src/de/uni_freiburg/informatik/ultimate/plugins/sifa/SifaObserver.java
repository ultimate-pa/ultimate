/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Sifa plug-in.
 *
 * The ULTIMATE Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.sifa;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain.ResultForAlteredInputs;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder.SifaComponents;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * Starts Sifa (symbolic interpretation with fluid abstractions) on an icfg.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class SifaObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private SifaComponents mSifaComponents;

	public SifaObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg<?>) {
			processIcfg((IIcfg<IcfgLocation>) root);
			return false;
		}
		return true;
	}

	private void processIcfg(final IIcfg<IcfgLocation> icfg) {
		mLogger.info(mServices.getPreferenceProvider(Activator.PLUGIN_ID).getSingleLinePreferenceString());
		mSifaComponents = new SifaBuilder(mServices, mLogger).construct(icfg, mServices.getProgressMonitorService());
		final Map<IcfgLocation, IPredicate> predicates = mSifaComponents.getIcfgInterpreter().interpret();
		reportStats(mSifaComponents.getStats());
		reportResults(predicates);
	}

	private void reportStats(final SifaStats stats) {
		final StatisticsData csvProvider = new StatisticsData();
		final String shortDescription = "Symbolic Interpretation with Fluid Abstractions";
		csvProvider.aggregateBenchmarkData(stats);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_ID, shortDescription, csvProvider));
	}

	private void reportResults(final Map<IcfgLocation, IPredicate> predicates) {
		boolean allSafe = true;
		for (final Map.Entry<IcfgLocation, IPredicate> loiPred : predicates.entrySet()) {
			allSafe &= reportSingleResult(loiPred);
		}
		if (allSafe) {
			mLogger.info("✔ All error locations are guaranteed to be unreachable.");
			mServices.getResultService().reportResult(Activator.PLUGIN_ID,
					new AllSpecificationsHoldResult(Activator.PLUGIN_ID, ""));
		} else {
			mLogger.info("✘ Some error locations might be reachable, see reported results.");
		}
	}

	/**
	 * @return The given location is safe, that is, its predicate is bottom.
	 */
	private boolean reportSingleResult(final Map.Entry<IcfgLocation, IPredicate> loiPred) {
		final ResultForAlteredInputs predEqBottom = mSifaComponents.getDomain().isEqBottom(loiPred.getValue());
		final IResult result;
		if (predEqBottom.isTrueForAbstraction()) {
			result = new PositiveResult<>(Activator.PLUGIN_ID, loiPred.getKey(), mServices.getBacktranslationService());
		} else {
			String msg = "Over-approximation of reachable states at this location is " + loiPred.getValue();
			if (predEqBottom.wasAbstracted()) {
				msg += "\nFinal emptiness check over-approximated again to " + predEqBottom.getLhs();
			}
			result = new UnprovableResult<>(Activator.PLUGIN_ID, loiPred.getKey(),
					mServices.getBacktranslationService(),
					IcfgProgramExecution.create(Collections.emptyList(), Collections.emptyMap()), msg);
		}
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		return predEqBottom.isTrueForAbstraction();
	}

}
