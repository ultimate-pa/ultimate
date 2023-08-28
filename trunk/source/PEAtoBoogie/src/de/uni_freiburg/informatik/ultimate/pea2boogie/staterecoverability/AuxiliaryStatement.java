package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxiliaryStatementContainer.StatementAssignment;

public interface AuxiliaryStatement {

	public Statement getStatement(StatementAssignment stRecExpr);

	public BoogieLocation setBoogieLocation(BoogieLocation loc);
	
	public BoogieLocation getBoogieLocation();
}
