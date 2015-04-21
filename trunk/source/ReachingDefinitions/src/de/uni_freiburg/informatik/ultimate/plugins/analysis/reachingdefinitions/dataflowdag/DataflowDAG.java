package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;

public class DataflowDAG<T> extends ModifiableLabeledEdgesMultigraph<DataflowDAG<T>, ScopedBoogieVar> {

	private static final long serialVersionUID = 1L;

	private T mNodeLabel;

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

	public void printGraphDebug(Logger logger) {
		for (String s : getDebugString().split("\n"))
			logger.debug(s);
	}

	public String getDebugString() {
		StringBuilder st = new StringBuilder();
		getDebugString(st, this, "", "");
		return st.toString();
	}

    private void getDebugString(StringBuilder st, DataflowDAG<T> dag, String edgeLabel, String ident) {
    	if (edgeLabel.isEmpty()) {
			st.append(dag + "\n");
		} else {
			st.append(ident + "--" + edgeLabel + "--> " + dag + "\n");
		}

		for (DataflowDAG<T> next : dag.getOutgoingNodes()) {
			getDebugString(st, next, dag.getOutgoingEdgeLabel(next).toString(), ident + "  ");
		}
    }

}
