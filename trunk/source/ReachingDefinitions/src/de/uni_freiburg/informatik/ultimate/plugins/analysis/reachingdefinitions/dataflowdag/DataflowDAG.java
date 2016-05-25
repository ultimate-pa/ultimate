/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;

public class DataflowDAG<T> extends ModifiableLabeledEdgesMultigraph<DataflowDAG<T>, ScopedBoogieVar> {

	private static final long serialVersionUID = 1L;

	private final T mNodeLabel;

	public DataflowDAG(T stmt) {
		mNodeLabel = stmt;
	}

	public T getNodeLabel() {
		return mNodeLabel;
	}

	@Override
	public String toString() {
		if (mNodeLabel == null) {
			return "NULL";
		}
		if (mNodeLabel instanceof Statement) {
			return "[" + mNodeLabel.hashCode() + "]: " + BoogiePrettyPrinter.print((Statement) mNodeLabel);
		}
		return "[" + mNodeLabel.hashCode() + "]: " + mNodeLabel.toString();
	}

	public void printGraphDebug(ILogger logger) {
		for (final String s : getDebugString().split("\n")) {
			logger.debug(s);
		}
	}

	public String getDebugString() {
		final StringBuilder st = new StringBuilder();
		getDebugString(st, this, "", "");
		return st.toString();
	}

    private void getDebugString(StringBuilder st, DataflowDAG<T> dag, String edgeLabel, String ident) {
    	if (edgeLabel.isEmpty()) {
			st.append(dag + "\n");
		} else {
			st.append(ident + "--" + edgeLabel + "--> " + dag + "\n");
		}

		for (final DataflowDAG<T> next : dag.getOutgoingNodes()) {
			getDebugString(st, next, dag.getOutgoingEdgeLabel(next).toString(), ident + "  ");
		}
    }

}
