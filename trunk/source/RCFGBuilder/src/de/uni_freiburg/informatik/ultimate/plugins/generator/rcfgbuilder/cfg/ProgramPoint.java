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

import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Node of a recursive control flow graph. This can be seen as
 * <ul>
 * <li>A Location of size zero.
 * <li>The startpoint of a location.
 * <li>A position in the program.
 * 
 * @author heizmann@informatik.uni-freiburg.
 */

public class ProgramPoint extends RCFGNode {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	private final BoogieASTNode m_BoogieASTNode;

	@Visualizable
	final private String m_Procedure;
	@Visualizable
	final private String m_Position;
	@Visualizable
	final private boolean m_IsErrorLocation;

	public ProgramPoint(String position, String procedure, boolean isErrorLoc,
			BoogieASTNode boogieASTNode) {
		super();
		this.m_Procedure = procedure;
		this.m_Position = position;
		this.m_IsErrorLocation = isErrorLoc;
		this.m_BoogieASTNode = boogieASTNode;

		ILocation loc = null;
		if (boogieASTNode instanceof Statement) {
			Statement st = (Statement) boogieASTNode;
			loc = st.getLocation();
		} else if (boogieASTNode instanceof Specification) {
			Specification spec = (Specification) boogieASTNode;
			loc = spec.getLocation();
		} else if (boogieASTNode instanceof Procedure) {
			loc = boogieASTNode.getLocation();
		}
		mPayload = new Payload(loc, position);
		String name = "Procedure: " + m_Procedure + " Position: " + m_Position;
		mPayload.setName(name);

	}

	/**
	 * @return the procedure
	 */
	public String getProcedure() {
		return m_Procedure;
	}

	/**
	 * @return the location
	 */
	public String getPosition() {
		return m_Position;
	}

	public boolean isErrorLocation() {
		return m_IsErrorLocation;
	}

	public BoogieASTNode getBoogieASTNode() {
		return m_BoogieASTNode;
	}

	public String getLocationName() {
		return getPosition();
	}

	public String BoogieASTNodeType() {
		if (m_BoogieASTNode instanceof AssertStatement) {
			return "AssertStatement";
		} else if (m_BoogieASTNode instanceof CallStatement) {
			return "RequiresSpecification";
		} else if (m_BoogieASTNode instanceof EnsuresSpecification) {
			return "EnsuresSpecification";
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public boolean addIncoming(RCFGEdge incoming) {
		if (incoming instanceof CodeBlock || incoming instanceof RootEdge) {
			return super.addIncoming(incoming);
		} else {
			throw new IllegalArgumentException(
					"predecessor has to be CodeBlock or RootEdge");
		}
	}

	@Override
	public boolean addOutgoing(RCFGEdge outgoing) {
		if (outgoing instanceof CodeBlock || outgoing instanceof RootEdge) {
			return super.addOutgoing(outgoing);
		} else {
			throw new IllegalArgumentException("successor has to be CodeBlock");
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof ProgramPoint) {
			ProgramPoint pp2 = (ProgramPoint) obj;
			return this.m_Procedure.equals(pp2.getProcedure())
					&& this.m_Position.equals(pp2.getPosition());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 3 * this.m_Position.hashCode() + 5 * this.m_Procedure.hashCode();
	}

	@Override
	public String toString() {
		return m_Position;
	}

}
