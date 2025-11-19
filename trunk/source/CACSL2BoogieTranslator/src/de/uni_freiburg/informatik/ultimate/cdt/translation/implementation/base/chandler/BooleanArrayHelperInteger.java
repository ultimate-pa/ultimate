package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class BooleanArrayHelperInteger implements IBooleanArrayHelper {

	@Override
	public ASTType constructBoolReplacementType() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new PrimitiveType(ignoreLoc, BoogieType.TYPE_INT, "int");
	}

	@Override
	public Expression constructTrue() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return ExpressionFactory.createIntegerLiteral(ignoreLoc, "1");
	}

	@Override
	public Expression constructFalse() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return ExpressionFactory.createIntegerLiteral(ignoreLoc, "0");
	}

	@Override
	public Expression compareWithTrue(final Expression expr) {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ, expr, constructTrue());
	}

}