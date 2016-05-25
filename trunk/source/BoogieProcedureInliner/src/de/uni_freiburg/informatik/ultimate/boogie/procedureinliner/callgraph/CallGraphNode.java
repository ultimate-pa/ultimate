/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;

/**
 * Node of a Boogie call graph.
 * A Node represents a procedure, where the directed edges are the calls inside this procedure.
 * Multiple calls to the same procedure occur multiple times. The order of all calls is preserved.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallGraphNode extends ModifiableLabeledEdgesMultigraph<CallGraphNode, CallGraphEdgeLabel> {
	
	private static final long serialVersionUID = -937014582193693103L;

	private final String mId;
	private Procedure mProcedureWithSpecification;
	private Procedure mProcedureWithBody;
	private CallGraphNodeLabel mLabel;
	
	public CallGraphNode(String id) {
		mId = id;
	}
	
	public String getId() {
		return mId;
	}
	
	public void setProcedureWithSpecification(Procedure p) {
		assert p == null || p.getIdentifier().equals(mId);
		assert p == null || p.getSpecification() != null;
		mProcedureWithSpecification = p;
	}
	
	public void setProcedureWithBody(Procedure p) {
		assert p == null || p.getIdentifier().equals(mId);
		assert p == null || p.getBody() != null;
		mProcedureWithBody = p;
	}

	public void setLabel(CallGraphNodeLabel label) {
		mLabel = label;
	}

	public Procedure getProcedureWithSpecification() {
		return mProcedureWithSpecification;
	}

	public Procedure getProcedureWithBody() {
		return mProcedureWithBody;
	}

	public CallGraphNodeLabel getLabel() {
		return mLabel;
	}
	
	public boolean isImplemented() {
		return mProcedureWithBody != null;
	}
	
	/**
	 * @return The procedure is declared and implemented in the same object.
	 * 		   {@link #getProcedureWithSpecification()} and {@link #getProcedureWithBody()} will return the same object;
	 */
	public boolean isCombined() {
		return mProcedureWithSpecification == mProcedureWithBody;
	}
	
	public boolean isPolymorphic() {
		return mProcedureWithSpecification.getTypeParams().length > 0;
	}
	
	/**
	 * Iterates over all outgoing edge labels, looking for set inline flags.
	 * @return A call statement inside the procedure should be inlined.
	 * @see CallGraphEdgeLabel#getInlineFlag()
	 */
	public boolean hasInlineFlags() {
		for (final CallGraphEdgeLabel edgeLabel : getOutgoingEdgeLabels()) {
			if (edgeLabel.getInlineFlag()) {
				return true;
			}
		}
		return false;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mId);
		sb.append('{');
		sb.append(isImplemented() ? "impl" : "unimpl");
		sb.append(',');
		sb.append(mLabel);
		sb.append('}');
		sb.append(getOutgoingEdgeLabels());
		return sb.toString();
	}
}
