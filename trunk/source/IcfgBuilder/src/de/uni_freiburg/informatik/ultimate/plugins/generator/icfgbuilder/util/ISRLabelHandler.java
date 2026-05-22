/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE IcfgBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.util;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/*
 * Traverse the ICFG belonging to an IDP with BFS and extract information about the locations belonging to
 * interrupt-service routines.
 */
public class ISRLabelHandler {

	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final Map<? extends IcfgLocation, Label> mLoc2Label;
	private final Map<IcfgLocation, IDPNodeLocation> mIcfgLoc2IsrLocType;

	private final ILogger mLogger;

	public ISRLabelHandler(final IIcfg<? extends IcfgLocation> icfg, final Map<? extends IcfgLocation, Label> loc2Label,
			final ILogger logger) {
		mLogger = logger;

		mIcfg = icfg;
		mLoc2Label = loc2Label;
		mIcfgLoc2IsrLocType = processIcfg();
	}

	private Map<IcfgLocation, IDPNodeLocation> processIcfg() {
		final HashMap<IcfgLocation, IDPNodeLocation> boogieLoc2IdpLoc = new HashMap<>();
		final HashDeque<Pair<IcfgLocation, IDPNodeLocation>> icfgNodes = new HashDeque<>();
		final var visited = new HashSet<IcfgLocation>();
		final var initNodes = mIcfg.getProcedureEntryNodes().values();
		final var idpMainProcLoc = new IDPNodeLocation(IDPLocation.MAIN, 0);
		for (final IcfgLocation IcfgLocation : initNodes) {
			icfgNodes.offer(new Pair<>(IcfgLocation, idpMainProcLoc));
		}
		while (!icfgNodes.isEmpty()) {
			final var currentPair = icfgNodes.poll();
			final var currentNode = currentPair.getFirst();
			var nodeLoc = currentPair.getSecond();
			if (!visited.add(currentNode)) {
				continue;
			}
			if (nodeLoc.location == IDPLocation.ISR_EXIT) {
				nodeLoc = idpMainProcLoc;
			} else if (isIsrLocation(currentNode)) {
				nodeLoc = getLocationISRType(currentNode);
			}
			boogieLoc2IdpLoc.put(currentNode, nodeLoc);
			final var edges = currentNode.getOutgoingEdges();
			for (final IcfgEdge icfgEdge : edges) {
				final var succNode = icfgEdge.getTarget();
				icfgNodes.offer(new Pair<>(succNode, nodeLoc));
			}
		}
		return boogieLoc2IdpLoc;
	}

	private boolean isIsrLocation(final IcfgLocation location) {
		final var label = mLoc2Label.get(location);
		return label != null;
	}

	private IDPNodeLocation getLocationISRType(final IcfgLocation location) {
		final var label = mLoc2Label.get(location);
		if (label == null) {
			return new IDPNodeLocation(IDPLocation.MAIN, 0);
		}
		return processISRLabel(label);
	}

	public Map<IcfgLocation, IDPNodeLocation> getIcfgLoc2IDPLoc() {
		return mIcfgLoc2IsrLocType;
	}

	private static IDPNodeLocation processISRLabel(final Label label) {
		final var attributes = label.getAttributes();

		assert attributes.length == 3 : "Label is not a proper ISR-label";

		final var labelType = attributes[0];
		assert labelType.getName() == "isr_label" : "Attribute of ISR-label " + label.getName() + " is invalid";
		final var labelLocation = attributes[1];
		final var labelNum = attributes[2];
		// TODO: Sanity checks?
		final var isrId = Integer.parseInt(labelNum.getName());
		if (labelLocation.getName().equals("entry")) {
			return new IDPNodeLocation(IDPLocation.ISR_ENTRY, isrId);
		}
		assert labelType.getName().equals("exit") : "Invalid attribute of ISR-label " + label.getName();
		return new IDPNodeLocation(IDPLocation.ISR_EXIT, isrId);
	}

	public IDPNodeLocation getIDPLocation(final IcfgLocation icfgLocation) {
		// TODO: Mabe return MAIN if the get results in null?
		return mIcfgLoc2IsrLocType.get(icfgLocation);
	}

	public record IDPNodeLocation(IDPLocation location, int isrId) {

	}

	public enum IDPLocation {
		ISR_ENTRY, ISR_EXIT, MAIN
	}
}
