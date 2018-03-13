/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Check given annotation without inferring invariants.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class InvariantChecker {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;
	private final IIcfg<IcfgLocation> mIcfg;

	public InvariantChecker(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final IIcfg<IcfgLocation> icfg) {
		mServices = services;
		mToolchainStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mIcfg = icfg;
		final Map<String, Set<IcfgLocation>> proc2errNodes = icfg.getProcedureErrorNodes();
		for (final Entry<String, Set<IcfgLocation>> entry : proc2errNodes.entrySet()) {
			for (final IcfgLocation errorLoc : entry.getValue()) {
				
				final ArrayDeque<IcfgLocation> worklistBackward = new ArrayDeque<>();
				final Set<IcfgLocation> seenBackward = new HashSet<>();
				final Set<IcfgLocation> startLocations = new HashSet<>();
				for (final IcfgLocation predLoc : errorLoc.getIncomingNodes()) {
					worklistBackward.add(predLoc);
				}
				IcfgLocation loc;
				while (!worklistBackward.isEmpty()) {
					loc = worklistBackward.removeFirst();
					for (final IcfgLocation predLoc : loc.getIncomingNodes()) {
						if (!seenBackward.contains(predLoc)) {
							seenBackward.add(predLoc);
							final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(predLoc);
							if (loa != null) {
								startLocations.add(predLoc);
							} else {
								if (icfg.getInitialNodes().contains(predLoc)) {
									startLocations.add(predLoc);
								} else {
									worklistBackward.add(predLoc);
								}
							}
						}
					}
				}
				for (final IcfgLocation startLoc : startLocations) {
					
				}
			}
		}
	}
}
