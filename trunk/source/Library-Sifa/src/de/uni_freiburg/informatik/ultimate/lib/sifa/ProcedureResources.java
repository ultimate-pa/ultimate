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
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexToDag;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.RegexStatUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Resources like dag and overlays for a single procedure.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class ProcedureResources {

	private final RegexDag<IIcfgTransition<IcfgLocation>> mRegexDag;
	private final BackwardClosedOverlay<IIcfgTransition<IcfgLocation>> mDagOverlayPathToReturn;
	private final BackwardClosedOverlay<IIcfgTransition<IcfgLocation>> mDagOverlayPathToLOIsAndEnterCalls;

	public ProcedureResources(final SifaStats stats, final IIcfg<IcfgLocation> icfg, final String procedure,
			final Collection<IcfgLocation> locationsOfInterest, final Collection<String> enterCallsOfInterest) {

		// TODO split this function into sub-functions

		final ProcedureGraph procedureGraph = new ProcedureGraphBuilder(stats, icfg)
				.graphOfProcedure(procedure, locationsOfInterest, enterCallsOfInterest);
		final Map<String, IcfgLocation> procedureEntryNodes = icfg.getProcedureEntryNodes();
		final IcfgLocation entry = procedureGraph.getEntryNode();
		final PathExpressionComputer<IcfgLocation,IIcfgTransition<IcfgLocation>> peComputer =
				RegexStatUtils.createPEComputer(stats, procedureGraph);
		final RegexToDag<IIcfgTransition<IcfgLocation>> regexToDag = RegexStatUtils.createRegexToDag(stats);

		final Collection<RegexDagNode<IIcfgTransition<IcfgLocation>>> loisAndEnterCallMarkers = new ArrayList<>(
				locationsOfInterest.size() + enterCallsOfInterest.size());
		locationsOfInterest.stream()
				.peek(loi -> assertLoiFromSameProcedure(procedure, loi))
				.map(loi -> markRegex(RegexStatUtils.exprBetween(stats, peComputer, entry, loi), loi))
				.map(regex -> RegexStatUtils.addToDag(stats, regexToDag, regex))
				.forEach(loisAndEnterCallMarkers::add);
		enterCallsOfInterest.stream()
				.map(procedureEntryNodes::get)
				.map(procEntry -> markRegex(RegexStatUtils.exprBetween(stats, peComputer, entry, procEntry), procEntry))
				.map(regex -> RegexStatUtils.addToDag(stats, regexToDag, regex))
				.forEach(loisAndEnterCallMarkers::add);

		final RegexDagNode<IIcfgTransition<IcfgLocation>> returnDagNode = RegexStatUtils.addToDag(stats, regexToDag,
			markRegex(
				RegexStatUtils.exprBetween(stats, peComputer, entry, procedureGraph.getExitNode()),
				procedureGraph.getExitNode()
			)
		);

		mRegexDag = RegexStatUtils.getDagAndReset(stats, regexToDag);
		RegexStatUtils.compress(stats, mRegexDag);

		mDagOverlayPathToLOIsAndEnterCalls = new BackwardClosedOverlay<>();
		// loiDagNodes and enterCallDagNodes are computed before dag compression,
		// but since they are unique using them after compression is safe
		loisAndEnterCallMarkers.stream()
				.forEach(mDagOverlayPathToLOIsAndEnterCalls::addExclusive);
		mDagOverlayPathToReturn = new BackwardClosedOverlay<>();
		mDagOverlayPathToReturn.addExclusive(returnDagNode);
	}

	/**  Marks a regex by appending a marker literal based on a location. */
	private static IRegex<IIcfgTransition<IcfgLocation>> markRegex(
			final IRegex<IIcfgTransition<IcfgLocation>> regex, final IcfgLocation finalLocationAsMark) {
		return Regex.concat(regex, Regex.literal(new LocationMarkerTransition(finalLocationAsMark)));
	}

	private static void assertLoiFromSameProcedure(final String procedure, final IcfgLocation loi) {
		assert procedure.equals(loi.getProcedure()) : "Location of interest from different procedure";
	}

	public RegexDag<IIcfgTransition<IcfgLocation>> getRegexDag() {
		return mRegexDag;
	}

	public IDagOverlay<IIcfgTransition<IcfgLocation>> getDagOverlayPathToReturn() {
		return mDagOverlayPathToReturn;
	}

	public IDagOverlay<IIcfgTransition<IcfgLocation>> getDagOverlayPathToLoisAndEnterCalls() {
		return mDagOverlayPathToLOIsAndEnterCalls;
	}
}
