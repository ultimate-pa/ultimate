package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

public interface IBooleanArrayHelper {
	ASTType constructBoolReplacementType();

	Expression constructTrue();

	Expression constructFalse();

	Expression compareWithTrue(Expression expr);

	default Expression constructFromValue(final boolean value) {
		return value ? constructTrue() : constructFalse();
	}
}