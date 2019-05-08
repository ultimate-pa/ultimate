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

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.ProcedureResources.OverlaySuccessors;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Annotates given program locations with predicates over-approximating the actually reachable concrete states at that
 * locations.
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class SymbolicInterpreter {

	private final IIcfg<IcfgLocation> mIcfg;
	private final CallGraph mCallGraph;
	private Map<String, ProcedureResources> mProcResources = new HashMap<>();

	public SymbolicInterpreter(final IIcfg<IcfgLocation> icfg) {
		mIcfg = icfg;
		mCallGraph = new CallGraph(icfg,
				icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toList()));
	}

	public SymbolicInterpreter(final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		mCallGraph = new CallGraph(icfg, locationsOfInterest);
	}

	public void interpret() {
		final Queue<String> procedureWorklist = new ArrayDeque<>(mCallGraph.initialProceduresOfInterest());
		while (!procedureWorklist.isEmpty()) {
			final String procedure = procedureWorklist.remove();
			final ProcedureResources resources = mProcResources.computeIfAbsent(procedure, this::computeProcResources);
			interpretLOIs(resources);
			// TODO add successors to procedureWorklist but ignore duplicates
		}
	}
	
	private void interpretLOIs(final ProcedureResources resources) {
		final RegexDag<IIcfgTransition<IcfgLocation>> dag = resources.getRegexDag();
		final OverlaySuccessors overlaySuccessors = resources.getDagOverlayPathToLOIsAndEnterCalls();
		final Queue<RegexDagNode<IIcfgTransition<IcfgLocation>>> worklist = new ArrayDeque<>();
		worklist.add(dag.getSource());
		while (!worklist.isEmpty()) {
			// TODO retrieve inputs, interpret current node, put outputs somewhere
			final RegexDagNode<IIcfgTransition<IcfgLocation>> currentNode = worklist.remove();
			// TODO add successors to worklist but ignore duplicates
		}
	}

	private ProcedureResources computeProcResources(final String procedure) {
		return new ProcedureResources(mIcfg, procedure, mCallGraph.locationsOfInterest(procedure),
				mCallGraph.successorsOfInterest(procedure));
	}
}
