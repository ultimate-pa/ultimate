package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class StatementFactory {

	public static AssignmentStatement constructAssignmentStatement(final ILocation loc, final LeftHandSide[] lhs,
			final Expression[] rhs) {

		final String[] lhsIds = new String[lhs.length];
		final BoogieType[] lhsTypes = new BoogieType[lhs.length];
		final BoogieType[] rhsTypes = new BoogieType[rhs.length];
		for (int i = 0; i < lhs.length; i++) {
			lhsIds[i] = TypeCheckHelper.getLeftHandSideIdentifier(lhs[i]);
			lhsTypes[i] = (BoogieType) lhs[i].getType();
			rhsTypes[i] = (BoogieType) rhs[i].getType();
			assert lhsTypes[i] != null;
			assert rhsTypes[i] != null;
		}

		TypeCheckHelper.typeCheckAssignStatement(lhsIds, lhsTypes, rhsTypes, new TypeErrorReporter(loc));

		return new AssignmentStatement(loc, lhs, rhs);
	}

}
