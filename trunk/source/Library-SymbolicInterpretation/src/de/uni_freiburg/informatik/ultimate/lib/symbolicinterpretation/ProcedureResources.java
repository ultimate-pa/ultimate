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

import java.util.Collection;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.ProcedureGraphBuilder;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.ProcedureGraph;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagCompressor;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexToDag;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class ProcedureResources {

	// TODO find a better way to abbreviate long generics
	public static class OverlaySuccessors extends HashRelation<
			RegexDagNode<IIcfgTransition<IcfgLocation>>, RegexDagNode<IIcfgTransition<IcfgLocation>>> {
	}

	private final RegexDag<IIcfgTransition<IcfgLocation>> mRegexDag;
	private final OverlaySuccessors mDagOverlayPathToReturn;
	private final OverlaySuccessors mDagOverlayPathToLOIsAndEnterCalls;

	public ProcedureResources(final IIcfg<IcfgLocation> icfg, final String procedure,
			final Collection<IcfgLocation> locationsOfInterest, final Collection<String> enterCallsOfInterest) {

		// TODO split this function into sub-functions

		final ProcedureGraph procedureGraph =
				new ProcedureGraphBuilder(icfg).graphOfProcedure(procedure, locationsOfInterest);
		final Map<String, IcfgLocation> procedureEntryNodes = icfg.getProcedureEntryNodes();
		final IcfgLocation entry = procedureGraph.getEntryNode();
		final PathExpressionComputer<IcfgLocation,IIcfgTransition<IcfgLocation>> peComputer =
				new PathExpressionComputer<>(procedureGraph);
		final RegexToDag<IIcfgTransition<IcfgLocation>> regexToDag = new RegexToDag<>();

		final Collection<RegexDagNode<IIcfgTransition<IcfgLocation>>> loiDagNodes = locationsOfInterest.stream()
				.peek(loi -> assertLoiFromSameProcedure(procedure, loi))
				.map(loi -> peComputer.exprBetween(entry, loi))
				.map(regexToDag::add)
				.collect(Collectors.toList());

		final Collection<RegexDagNode<IIcfgTransition<IcfgLocation>>> enterCallDagNodes = enterCallsOfInterest.stream()
				.map(procedureEntryNodes::get)
				.map(enterCallOfInterest -> peComputer.exprBetween(entry, enterCallOfInterest))
				.map(regexToDag::add)
				.collect(Collectors.toList());

		final RegexDagNode<IIcfgTransition<IcfgLocation>> returnDagNode =
				regexToDag.add(peComputer.exprBetween(entry, procedureGraph.getExitNode()));

		mRegexDag = regexToDag.getDag();
		new RegexDagCompressor<IIcfgTransition<IcfgLocation>>().compress(mRegexDag);

		mDagOverlayPathToLOIsAndEnterCalls = new OverlaySuccessors();
		Stream.concat(loiDagNodes.stream(), enterCallDagNodes.stream())
				.forEach(node -> addToOverlay(mDagOverlayPathToLOIsAndEnterCalls, node));
		mDagOverlayPathToReturn = new OverlaySuccessors();
		addToOverlay(mDagOverlayPathToReturn, returnDagNode);
	}

	private static void assertLoiFromSameProcedure(final String procedure, final IcfgLocation loi) {
		assert procedure.equals(loi.getProcedure()) : "Location of interest from different procedure";
	}

	private static void addToOverlay(final OverlaySuccessors overlaySuccessors,
			final RegexDagNode<IIcfgTransition<IcfgLocation>> targetNode) {
		for (final RegexDagNode<IIcfgTransition<IcfgLocation>> predecessor : targetNode.getIncomingNodes()) {
			if (overlaySuccessors.addPair(predecessor, targetNode)) {
				addToOverlay(overlaySuccessors, predecessor);
			}
		}
	}

	public RegexDag<IIcfgTransition<IcfgLocation>> getRegexDag() {
		return mRegexDag;
	}

	public OverlaySuccessors getDagOverlayPathToReturn() {
		return mDagOverlayPathToReturn;
	}

	public OverlaySuccessors getDagOverlayPathToLOIsAndEnterCalls() {
		return mDagOverlayPathToLOIsAndEnterCalls;
	}

}