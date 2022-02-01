/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
/**
 * This package provides a framework for the constraint-based synthesis of
 * safety invariants, ranking functions, danger invariants, recurrence sets,
 * etc.
 *
 * @author Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Jan Oreans (oreansj@cs.uni-freiburg.de)
 *
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.synthesis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

public class Starter {

	public Starter(IIcfg<IcfgLocation> icfg) {
		System.out.println("Start Starter");
		// IIcfg<IcfgLocation> mIcfg = icfg;
		// int numOfLocations = 0;
		// for (HashMap<String,IcfgLocation> i : icfg.mLocNodes.values()) {
		// 	numOfLocations = numOfLocations + i.size();
		// }
		
		Map<String, Map<DebugIdentifier, IcfgLocation>> locations = icfg.getProgramPoints();
		int numberOfLocations = locations.size();
		
		
		List<IcfgEdge> edges = new ArrayList<>();
		for (final Entry<String, Map<DebugIdentifier, IcfgLocation>> entry : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, IcfgLocation> innerEntry : entry.getValue().entrySet()) {
				final IcfgLocation loc = innerEntry.getValue();
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					edges.add(edge);
				}
			}
		}
		System.out.println("End Starter");
		// TODO(Daniel): Create edge list, variable names and number of locations
		
		// TODO: Create Strategy
		Strategy s = new Strategy(icfg);
		// Loop
		// -----
		
		// TODO(Jan): buildTerm
		
		// TODO: Linearisierer
		
		// TODO: Mozkin
		
		// TODO: SMT
		
		// TODO: Startegy.complicate()
		
	}
	
}
