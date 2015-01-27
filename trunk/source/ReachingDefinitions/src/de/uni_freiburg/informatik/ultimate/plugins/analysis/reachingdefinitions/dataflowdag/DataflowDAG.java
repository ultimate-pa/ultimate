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
		printDebugDAG(logger, this, "", "");
	}

	private void printDebugDAG(Logger logger, DataflowDAG<T> dag, String edgeLabel, String ident) {
		if (edgeLabel.isEmpty()) {
			logger.debug(dag);
		} else {
			logger.debug(ident + "--" + edgeLabel + "--> " + dag);
		}

		for (DataflowDAG<T> next : dag.getOutgoingNodes()) {
			printDebugDAG(logger, next, dag.getOutgoingEdgeLabel(next).toString(), ident + "  ");
		}
	}

}
