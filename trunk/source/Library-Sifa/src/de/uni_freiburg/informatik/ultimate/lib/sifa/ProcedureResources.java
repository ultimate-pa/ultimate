/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.ProcedureGraph;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.ProcedureGraphBuilder;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.BackwardClosedOverlay;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.IDagOverlay;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDagUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexToDag;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.RegexStatUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Resources like DAG and DAG overlays for a single procedure.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class ProcedureResources {

	private final RegexDag<IIcfgTransition<IcfgLocation>> mRegexDag;
	/**
	 * @see #getDagOverlayPathToReturn()
	 */
	private final BackwardClosedOverlay<IIcfgTransition<IcfgLocation>> mDagOverlayPathToReturn;
	/**
	 * @see #getDagOverlayPathToLoisAndEnterCalls()
	 */
	private final BackwardClosedOverlay<IIcfgTransition<IcfgLocation>> mDagOverlayPathToLOIsAndEnterCalls;

	public ProcedureResources(final SifaStats stats, final IIcfg<IcfgLocation> icfg, final String procedure,
			final Collection<IcfgLocation> locationsOfInterest, final Collection<String> enterCallsOfInterest) {

		// TODO split this function for readability

		final ProcedureGraph procedureGraph = new ProcedureGraphBuilder(stats, icfg)
				.graphOfProcedure(procedure, locationsOfInterest, enterCallsOfInterest);
		final Map<String, IcfgLocation> procedureEntryNodes = icfg.getProcedureEntryNodes();
		final IcfgLocation entry = procedureGraph.getEntryNode();
		final PathExpressionComputer<IcfgLocation,IIcfgTransition<IcfgLocation>> peComputer =
				RegexStatUtils.createPEComputer(stats, procedureGraph);
		final RegexToDag<IIcfgTransition<IcfgLocation>> regexToDag = RegexStatUtils.createRegexToDag(stats);

		final Collection<RegexDagNode<IIcfgTransition<IcfgLocation>>> loiMarkers =
				new ArrayList<>(locationsOfInterest.size());
		final Collection<RegexDagNode<IIcfgTransition<IcfgLocation>>> enterCallMarkers =
				// pre-sizing assumes that procedures are called up to two times
				new ArrayList<>(2 * enterCallsOfInterest.size());
		
		locationsOfInterest.stream()
				.peek(loi -> assertLoiFromSameProcedure(procedure, loi))
				.map(loi -> RegexDagUtils.markRegex(RegexStatUtils.exprBetween(stats, peComputer, entry, loi), loi))
				.map(regex -> RegexStatUtils.addToDag(stats, regexToDag, regex))
				.forEach(loiMarkers::add);
		enterCallsOfInterest.stream()
				.map(procedureEntryNodes::get)
				.map(procEntry -> RegexDagUtils.markRegex(RegexStatUtils.exprBetween(stats, peComputer, entry, procEntry), procEntry))
				.map(regex -> RegexStatUtils.addToDag(stats, regexToDag, regex))
				.forEach(enterCallMarkers::add);

		IcfgLocation exitNode = procedureGraph.getExitNode().orElse(null);
		final IRegex<IIcfgTransition<IcfgLocation>> regexToReturn = exitNode == null ?
				Regex.emptySet() : RegexStatUtils.exprBetween(stats, peComputer, entry, exitNode);
		final RegexDagNode<IIcfgTransition<IcfgLocation>> returnDagNode = RegexStatUtils.addToDag(stats, regexToDag,
				RegexDagUtils.markRegex(regexToReturn, exitNode));

		mRegexDag = RegexStatUtils.getDagAndReset(stats, regexToDag);
		RegexStatUtils.compress(stats, mRegexDag);

		mDagOverlayPathToLOIsAndEnterCalls = new BackwardClosedOverlay<>();
		// loiDagNodes and enterCallDagNodes are computed before DAG compression,
		// but since they are unique using them after compression is safe
		loiMarkers.forEach(mDagOverlayPathToLOIsAndEnterCalls::addInclusive);
		enterCallMarkers.forEach(mDagOverlayPathToLOIsAndEnterCalls::addExclusive);
		mDagOverlayPathToReturn = new BackwardClosedOverlay<>();
		mDagOverlayPathToReturn.addInclusive(returnDagNode);
	}

	private static void assertLoiFromSameProcedure(final String procedure, final IcfgLocation loi) {
		assert procedure.equals(loi.getProcedure()) : "Location of interest from different procedure";
	}

	public RegexDag<IIcfgTransition<IcfgLocation>> getRegexDag() {
		return mRegexDag;
	}

	/**
	 * Returns the DAG overlay where only nodes and edges leading to this procedure's exit location are included.
	 * The overlay contains exactly one marker ({@link LocationMarkerTransition}). The marker marks the exit location.
	 * 
	 * @return Overlay for exit node of procedure
	 */
	public IDagOverlay<IIcfgTransition<IcfgLocation>> getDagOverlayPathToReturn() {
		return mDagOverlayPathToReturn;
	}
	
	/**
	 * Returns the DAG overlay where only nodes and edges are included that
	 * <ul>
	 * <li>either lead to a LOI in this procedure
	 * <li>or lead to an enter call of interest (specified in the constructor) in the procedure.
	 * <ul>
	 * LOIs are marked ({@link LocationMarkerTransition}).
	 * Enter calls are not marked to differentiate them from LOIs. Enter calls can be identified by their
	 * transition type ({@link IIcfgCallTransition}).
	 * 
	 * @return Overlay for LOIs and enter calls in procedure
	 */
	public IDagOverlay<IIcfgTransition<IcfgLocation>> getDagOverlayPathToLoisAndEnterCalls() {
		return mDagOverlayPathToLOIsAndEnterCalls;
	}
}
