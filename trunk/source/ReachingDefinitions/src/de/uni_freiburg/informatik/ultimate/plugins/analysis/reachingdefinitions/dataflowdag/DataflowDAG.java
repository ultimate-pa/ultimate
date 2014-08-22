package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableLabeledEdgesMultigraph;

public class DataflowDAG extends ModifiableLabeledEdgesMultigraph<DataflowDAG, IdentifierExpression> {

	private static final long serialVersionUID = 1L;

	private Statement mStatement;

	public DataflowDAG(Statement stmt) {
		mStatement = stmt;
	}
	
	public Statement getStatement(){
		return mStatement;
	}

}
