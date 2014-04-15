package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.Payload;
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

	final private String m_Procedure;
	final private String m_Position;
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
		String name = "Procedure: " + m_Procedure + "Position: " + m_Position;
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
