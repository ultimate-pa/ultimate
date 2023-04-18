/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;

public class ChcProviderConcurrentWithSleep extends ChcProviderConcurrent {
	private final IUltimateServiceProvider mServices;

	public ChcProviderConcurrentWithSleep(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final HcSymbolTable hcSymbolTable, final ConcurrencyMode mode, final int level) {
		super(mgdScript, hcSymbolTable, mode, level);
		mServices = services;
	}

	@Override
	protected ThreadModularHornClauseProvider createFactory(final Map<String, Integer> numberOfThreads,
			final IIcfg<IcfgLocation> icfg) {
		final var independence = new SemanticIndependenceRelation<>(mServices, mMgdScript, false, true);
		final var locations = icfg.getProgramPoints().entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getKey, e -> e.getValue().values()));
		return new SleepSetThreadModularHornClauseProvider(numberOfThreads, mMgdScript, icfg.getCfgSmtToolkit(),
				mHcSymbolTable, x -> true, independence, locations);
	}
}
