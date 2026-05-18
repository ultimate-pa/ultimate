/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/*
 * Node of an ICFG for an interrupt-driven program that additionally stores whether the node belongs to an ISR of the
 * original program or the main routine. Additionally the node stores the position in ISR, i.e. is the node part of the
 * atomically executed ISR or is it part of the encapsulating outer while loop and which ISR it belongs to.
 */
public class BoogieIsrLocation extends BoogieIcfgLocation {

	private final ISRLocationType mLocationType;

	public BoogieIsrLocation(final DebugIdentifier debugIdentifier, final String procedure, final boolean isErrorLoc,
			final BoogieASTNode boogieASTNode, final ISRLocationType locationType) {
		super(debugIdentifier, procedure, isErrorLoc, boogieASTNode);
		mLocationType = locationType;
	}

	public ISRLocationType getLocationType() {
		return mLocationType;
	}

	public record ISRLocationType(ISRLocation location, int isrId) {

	}

	enum ISRLocation {
		OUTER_ENTRY, OUTER_EXIT, INNER_ENTRY, INNER_EXIT, MAIN
	}
}
