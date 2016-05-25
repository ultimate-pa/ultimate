/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 * Construct deep copy of an Boogie AST.
 * 
 * @author Matthias Heizmann
 * 
 */
public class BoogieAstCopier extends BoogieTransformer {

	public Unit copy(Unit unit) {
		final Declaration[] oldDeclarations = unit.getDeclarations();
		final Declaration[] newDeclarations = new Declaration[oldDeclarations.length];
		for (int i = 0; i < oldDeclarations.length; i++) {
			newDeclarations[i] = processDeclaration(oldDeclarations[i]);
			ModelUtils.copyAnnotations(oldDeclarations[i], newDeclarations[i]);
		}
		final Unit newUnit = new Unit(unit.getLocation(), newDeclarations);
		ModelUtils.copyAnnotations(unit, newUnit);
		return newUnit;
	}

	@Override
	protected Expression processExpression(Expression expr) {
		final Expression result;
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression idExpr = (IdentifierExpression) expr;
			final IdentifierExpression resultIdExpr = new IdentifierExpression(idExpr.getLocation(), idExpr.getIdentifier());
			final DeclarationInformation declInf = idExpr.getDeclarationInformation();
			if (declInf != null) {
				resultIdExpr.setDeclarationInformation(declInf);
			}
			result = resultIdExpr;
		} else if (expr instanceof BooleanLiteral) {
			final BooleanLiteral boolLit = (BooleanLiteral) expr;
			result = new BooleanLiteral(boolLit.getLocation(), boolLit.getType(), boolLit.getValue());
		} else if (expr instanceof IntegerLiteral) {
			final IntegerLiteral intLit = (IntegerLiteral) expr;
			result = new IntegerLiteral(intLit.getLocation(), intLit.getType(), intLit.getValue());
		} else if (expr instanceof BitvecLiteral) {
			final BitvecLiteral bitvecLit = (BitvecLiteral) expr;
			result = new BitvecLiteral(bitvecLit.getLocation(), bitvecLit.getType(), bitvecLit.getValue(),
					bitvecLit.getLength());
		} else if (expr instanceof StringLiteral) {
			final StringLiteral stringLit = (StringLiteral) expr;
			result = new StringLiteral(stringLit.getLocation(), stringLit.getType(), stringLit.getValue());
		} else if (expr instanceof WildcardExpression) {
			result = new WildcardExpression(expr.getLocation(), expr.getType());
		} else {
			result = super.processExpression(expr);
		}
		ModelUtils.copyAnnotations(expr, result);
		return result;
	}
}
