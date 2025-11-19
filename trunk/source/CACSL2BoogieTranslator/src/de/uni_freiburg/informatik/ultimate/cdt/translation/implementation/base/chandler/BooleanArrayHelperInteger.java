/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
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