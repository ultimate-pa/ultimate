/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * {@link IcfgLocation} of an ICFG that was obtained directly from a Boogie program
 * 
 * @author heizmann@informatik.uni-freiburg.
 */

public class BoogieIcfgLocation extends IcfgLocation {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	private final BoogieASTNode mBoogieASTNode;

	@Visualizable
	private final boolean mIsErrorLocation;

	public BoogieIcfgLocation(final String debugIdentifier, final String procedure, final boolean isErrorLoc,
			final BoogieASTNode boogieASTNode) {
		super(debugIdentifier, procedure, new Payload(getLocationFromASTNode(boogieASTNode)));
		mIsErrorLocation = isErrorLoc;
		mBoogieASTNode = boogieASTNode;
	}

	private static ILocation getLocationFromASTNode(final BoogieASTNode node) {
		final ILocation loc;
		if (node instanceof Statement) {
			final Statement st = (Statement) node;
			loc = st.getLocation();
		} else if (node instanceof Specification) {
			final Specification spec = (Specification) node;
			loc = spec.getLocation();
		} else if (node instanceof Procedure) {
			loc = node.getLocation();
		} else {
			loc = null;
		}
		return loc;
	}

	public boolean isErrorLocation() {
		return mIsErrorLocation;
	}

	public BoogieASTNode getBoogieASTNode() {
		return mBoogieASTNode;
	}

	public String BoogieASTNodeType() {
		if (mBoogieASTNode instanceof AssertStatement) {
			return "AssertStatement";
		} else if (mBoogieASTNode instanceof CallStatement) {
			return "RequiresSpecification";
		} else if (mBoogieASTNode instanceof EnsuresSpecification) {
			return "EnsuresSpecification";
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public boolean addIncoming(final IcfgEdge incoming) {
		if (incoming instanceof CodeBlock || incoming instanceof RootEdge) {
			return super.addIncoming(incoming);
		}
		throw new IllegalArgumentException("predecessor has to be CodeBlock or RootEdge");
	}

	@Override
	public boolean addOutgoing(final IcfgEdge outgoing) {
		if (outgoing instanceof CodeBlock || outgoing instanceof RootEdge) {
			return super.addOutgoing(outgoing);
		}
		throw new IllegalArgumentException("successor has to be CodeBlock");
	}

}
