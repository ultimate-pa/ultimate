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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;

/*
 * Traverse the ICFG belonging to an IDP with BFS and extract information about the locations belonging to
 * interrupt-service routines.
 */
public class ISRLabelHandler implements IStorable {

	private final IIcfg<BoogieIcfgLocation> mIcfg;
	private final Map<IcfgLocation, IDPNodeLocation> mIcfgLoc2IsrLocType;
	private final BoogieDeclarations mBoogieDeclarations;
	private final Map<Statement, Integer> mIsrId2Statements;

	private final ILogger mLogger;

	public ISRLabelHandler(final IIcfg<BoogieIcfgLocation> icfg, final BoogieDeclarations boogieDeclarations,
			final ILogger logger) {
		mLogger = logger;

		mIcfg = icfg;
		mBoogieDeclarations = boogieDeclarations;
		mIsrId2Statements = getInterruptStatements();
		mIcfgLoc2IsrLocType = processIcfg();
	}

	private Map<IcfgLocation, IDPNodeLocation> processIcfg() {
		final HashMap<IcfgLocation, IDPNodeLocation> boogieLoc2IdpLoc = new HashMap<>();
		final HashDeque<BoogieIcfgLocation> icfgNodes = new HashDeque<>();
		final var visited = new HashSet<IcfgLocation>();
		final var initNodes = mIcfg.getProcedureEntryNodes().values();
		for (final BoogieIcfgLocation IcfgLocation : initNodes) {
			icfgNodes.offer(IcfgLocation);
		}
		while (!icfgNodes.isEmpty()) {
			final BoogieIcfgLocation currentNode = icfgNodes.poll();
			if (!visited.add(currentNode)) {
				continue;
			}
			final var nodeLoc = getLocationISRType(currentNode);
			final var edges = currentNode.getOutgoingEdges();
			for (final IcfgEdge icfgEdge : edges) {
				final var succ = icfgEdge.getTarget();
				if (succ instanceof final BoogieIcfgLocation boogieIcfgLocation) {
					icfgNodes.offer(boogieIcfgLocation);
				}
				assert succ instanceof BoogieIcfgLocation;
			}
			boogieLoc2IdpLoc.put(currentNode, nodeLoc);
		}
		return boogieLoc2IdpLoc;
	}

	private boolean isIsrLocation(final BoogieIcfgLocation location) {
		if (location.getBoogieASTNode() instanceof final Statement st) {
			return mIsrId2Statements.containsKey(st);
		}
		return false;
	}

	private IDPNodeLocation getLocationISRType(final BoogieIcfgLocation location) {
		final var astNode = location.getBoogieASTNode();
		if (!isIsrLocation(location)) {
			return new IDPNodeLocation(IDPLocation.MAIN, 0);
		}
		final var st = (Statement) astNode;
		return new IDPNodeLocation(IDPLocation.ISR, mIsrId2Statements.get(st));
	}

	public Map<IcfgLocation, IDPNodeLocation> getIcfgLoc2IDPLoc() {
		return mIcfgLoc2IsrLocType;
	}

	private static boolean isISRLabel(final Label label) {
		final var attributes = label.getAttributes();
		if (attributes == null || attributes.length != 3) {
			return false;
		}
		final var attributeName = attributes[0].getName();
		return attributeName.equals("isr_label");
	}

	private static boolean isISREntry(final Label label) {
		final var attributes = label.getAttributes();
		if (attributes == null || attributes.length != 3) {
			return false;
		}
		final var attributeName = attributes[1].getName();
		return attributeName.equals("entry");
	}

	private Map<Statement, Integer> getInterruptStatements() {
		final var isrId2Statements = new HashMap<Statement, Integer>();
		for (final String procName : mBoogieDeclarations.getProcSpecification().keySet()) {
			if (mBoogieDeclarations.getProcImplementation().containsKey(procName)) {
				final var stmt = mBoogieDeclarations.getProcImplementation().get(procName).getBody().getBlock();
				final var procId2Isr = getInterruptStatements(stmt);
				isrId2Statements.putAll(procId2Isr);
			}
		}
		return isrId2Statements;
	}

	private static Map<Statement, Integer> getInterruptStatements(final Statement[] block) {
		final var isrId2Statements = new HashMap<Statement, Integer>();
		var currentIsrNum = -1;
		var isPartOfIsr = false;
		for (final Statement st : block) {
			if (isPartOfIsr) {
				assert currentIsrNum >= 0;
				final var prevVal = isrId2Statements.put(st, currentIsrNum);
				assert prevVal == null;
			}
			if (st instanceof final Label laSt) {
				if (!isISRLabel(laSt)) {
					continue;
				} else if (isISREntry(laSt)) {
					assert !isPartOfIsr : "Nested ISR labels are invalid!";
					isPartOfIsr = true;
					final var attributes = laSt.getAttributes();
					final var labelNum = attributes[2];
					currentIsrNum = Integer.parseInt(labelNum.getName());
					final var prevVal = isrId2Statements.put(st, currentIsrNum);
					assert prevVal == null;
				} else {
					isPartOfIsr = false;
				}
			}
		}
		return isrId2Statements;
	}

	public IDPNodeLocation getIDPLocation(final IcfgLocation icfgLocation) {
		// TODO: Maybe return MAIN if the get results in null?
		return mIcfgLoc2IsrLocType.get(icfgLocation);
	}

	public record IDPNodeLocation(IDPLocation location, int isrId) {

	}

	public enum IDPLocation {
		ISR, MAIN
	}

	@Override
	public void destroy() {
		// TODO Auto-generated method stub

	}
}
