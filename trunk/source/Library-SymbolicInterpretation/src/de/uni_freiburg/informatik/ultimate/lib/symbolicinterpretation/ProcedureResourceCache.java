/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class ProcedureResourceCache {

	private final CallGraph mCallGraph;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Map<String, ProcedureResources> mProcResources = new HashMap<>();

	public ProcedureResourceCache(final CallGraph callGraph, final IIcfg<IcfgLocation> icfg) {
		mCallGraph = callGraph;
		mIcfg = icfg;
	}

	public ProcedureResources resourcesOf(final String procedure) {
		return mProcResources.computeIfAbsent(procedure, this::computeProcResources);
	}

	private ProcedureResources computeProcResources(final String procedure) {
		return new ProcedureResources(mIcfg, procedure, mCallGraph.locationsOfInterest(procedure),
				mCallGraph.successorsOfInterest(procedure));
	}
}
