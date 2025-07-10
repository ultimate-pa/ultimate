package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class BooleanArrayHelper_Bool implements IBooleanArrayHelper {

	@Override
	public ASTType constructBoolReplacementType() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new PrimitiveType(ignoreLoc, BoogieType.TYPE_BOOL, "bool");
	}

	@Override
	public Expression constructTrue() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return ExpressionFactory.createBooleanLiteral(ignoreLoc, true);
	}

	@Override
	public Expression constructFalse() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return ExpressionFactory.createBooleanLiteral(ignoreLoc, false);
	}

	@Override
	public Expression compareWithTrue(final Expression expr) {
		return expr;
	}

}