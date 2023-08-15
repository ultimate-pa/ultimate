package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxStatementContainer.StRecExpr;

public interface AuxStatement {
	
	public Statement getStatement(StRecExpr stRecExpr);
	public BoogieLocation setBoogieLocation(BoogieLocation loc);
	public BoogieLocation getBoogieLocation();
}
