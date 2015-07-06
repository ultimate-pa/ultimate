/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;

/**
 * @author Thomas Lang
 *
 */
public class BitvectorWorkaroundOperationTranslator implements
		IOperationTranslator {

	@Override
	public String opTranslation(BinaryExpression.Operator op, IType type1, IType type2) {
		if (op == BinaryExpression.Operator.COMPEQ) {
			// if
			// (binexp.getLeft().getType().equals(PrimitiveType.boolType))
			return "=";
			// else
			// return script.equals(translateTerm(binexp.getLeft()),
			// translateTerm(binexp.getRight()));
		} else if (op == BinaryExpression.Operator.COMPGEQ) {
			return "bvsge";
		} else if (op == BinaryExpression.Operator.COMPGT) {
			return "bvsgt";
		} else if (op == BinaryExpression.Operator.COMPLEQ) {
			return "bvsle";
		} else if (op == BinaryExpression.Operator.COMPLT) {
			return "bvslt";
		} else if (op == BinaryExpression.Operator.COMPNEQ) {
		    throw new UnsupportedOperationException();
			// } else if (op == BinaryExpression.Operator.COMPPO ){
			// return script.atom(partOrder,
			// translateTerm(binexp.getLeft()),
			// translateTerm(binexp.getRight()));
		} else if (op == BinaryExpression.Operator.LOGICAND) {
			return "bvand";
		} else if (op == BinaryExpression.Operator.LOGICOR) {
			return "bvor";
		} else if (op == BinaryExpression.Operator.LOGICIMPLIES) {
			return "=>";
		} else if (op == BinaryExpression.Operator.LOGICIFF) {
			return "=";
		} else if (op == BinaryExpression.Operator.ARITHDIV) {
			if (type1 instanceof PrimitiveType) {
				PrimitiveType primType = (PrimitiveType) type1;
				if (primType.getTypeCode() == PrimitiveType.INT) {
					return "div";
				} else if (primType.getTypeCode() == PrimitiveType.REAL) {
					return "/";
				} else {
					throw new AssertionError("ARITHDIV of this type not allowed");
				}
			} else {
				throw new AssertionError("ARITHDIV of this type not allowed");
			}
		} else if (op == BinaryExpression.Operator.ARITHMINUS) {
			return "bvsub";
		} else if (op == BinaryExpression.Operator.ARITHMOD) {
			return "bvsmod";
		} else if (op == BinaryExpression.Operator.ARITHMUL) {
		    return "bvmul";
		} else if (op == BinaryExpression.Operator.ARITHPLUS) {
			return "bvadd";
		} else if (op == BinaryExpression.Operator.BITVECCONCAT) {
			return "concat";
		} else {
			throw new AssertionError("Unsupported binary expression " + op);
		}
	}

	@Override
	public String opTranslation(UnaryExpression.Operator op, IType type) {
		if (op == UnaryExpression.Operator.LOGICNEG) {
			return "not";
		} else if (op == UnaryExpression.Operator.ARITHNEGATIVE) {
			// FunctionSymbol fun_symb = script.getFunction("-", intSort);
			return "bvneg";
		} else
			throw new AssertionError("Unsupported unary expression " + op);
	}
}
