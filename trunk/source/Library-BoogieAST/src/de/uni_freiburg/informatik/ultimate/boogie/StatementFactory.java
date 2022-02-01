/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Creates Boogie statements. Difference to the corresponding constructors: does type checks and other sanity checks.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StatementFactory {


	public static AssignmentStatement constructSingleAssignmentStatement(final ILocation loc, final LeftHandSide lhs,
			final Expression rhs) {
		return constructAssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
	}

	public static AssignmentStatement constructAssignmentStatement(final ILocation loc, final LeftHandSide[] lhs,
			final Expression[] rhs) {
		assert lhs.length == rhs.length;
		assert lhs.length > 0;

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


	public static CallStatement constructCallStatement(final ILocation loc, final boolean isForall,
			final VariableLHS[] variableLHSs, final String methodName, final Expression[] arguments) {
		return new CallStatement(loc, isForall, variableLHSs, methodName, arguments);
	}

	public static Statement constructIfStatement(final ILocation loc, final Expression condition,
			final Statement[] thenPart, final Statement[] elsePart) {
		return new IfStatement(loc, condition, thenPart, elsePart);
	}

}
