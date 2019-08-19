/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Assists in the translation process in Expression2Term by covering the cases of operators, functions and literals.
 *
 * @author Thomas Lang
 *
 */
public class DefaultOperationTranslator implements IOperationTranslator {

	protected final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	protected final Script mScript;

	public DefaultOperationTranslator(final Boogie2SmtSymbolTable symbolTable, final Script script) {
		mBoogie2SmtSymbolTable = symbolTable;
		mScript = script;
	}

	@Override
	public String opTranslation(final BinaryExpression.Operator op, final IBoogieType type1, final IBoogieType type2) {
		if (op == BinaryExpression.Operator.COMPEQ) {
			return "=";
		} else if (op == BinaryExpression.Operator.COMPGEQ) {
			return ">=";
		} else if (op == BinaryExpression.Operator.COMPGT) {
			return ">";
		} else if (op == BinaryExpression.Operator.COMPLEQ) {
			return "<=";
		} else if (op == BinaryExpression.Operator.COMPLT) {
			return "<";
		} else if (op == BinaryExpression.Operator.COMPNEQ) {
			throw new UnsupportedOperationException();
		} else if (op == BinaryExpression.Operator.LOGICAND) {
			return "and";
		} else if (op == BinaryExpression.Operator.LOGICOR) {
			return "or";
		} else if (op == BinaryExpression.Operator.LOGICIMPLIES) {
			return "=>";
		} else if (op == BinaryExpression.Operator.LOGICIFF) {
			return "=";
		} else if (op == BinaryExpression.Operator.ARITHDIV) {
			final IBoogieType type = type1 == null ? type2 : type1;
			if (type instanceof BoogiePrimitiveType) {
				final BoogiePrimitiveType primType = (BoogiePrimitiveType) type;
				if (primType.getTypeCode() == BoogiePrimitiveType.INT) {
					return "div";
				} else if (primType.getTypeCode() == BoogiePrimitiveType.REAL) {
					return "/";
				} else {
					throw new AssertionError("ARITHDIV of this type not allowed: " + type);
				}
			}
			throw new AssertionError("ARITHDIV of this type not allowed: " + type);
		} else if (op == BinaryExpression.Operator.ARITHMINUS) {
			return "-";
		} else if (op == BinaryExpression.Operator.ARITHMOD) {
			return "mod";
		} else if (op == BinaryExpression.Operator.ARITHMUL) {
			return "*";
		} else if (op == BinaryExpression.Operator.ARITHPLUS) {
			return "+";
		} else if (op == BinaryExpression.Operator.BITVECCONCAT) {
			return "concat";
		} else {
			throw new AssertionError("Unsupported binary expression " + op);
		}
	}

	@Override
	public String opTranslation(final UnaryExpression.Operator op, final IBoogieType type) {
		if (op == UnaryExpression.Operator.LOGICNEG) {
			return "not";
		} else if (op == UnaryExpression.Operator.ARITHNEGATIVE) {
			return "-";
		} else {
			throw new AssertionError("Unsupported unary expression " + op);
		}
	}

	@Override
	public String funcApplication(final String funcIdentifier, final IBoogieType[] argumentTypes) {
		return mBoogie2SmtSymbolTable.getBoogieFunction2SmtFunction().get(funcIdentifier);
	}

	@Override
	public Term booleanTranslation(final BooleanLiteral exp) {
		return exp.getValue() ? mScript.term("true") : mScript.term("false");
	}

	@Override
	public Term bitvecTranslation(final BitvecLiteral exp) {
		final BigInteger[] indices = { BigInteger.valueOf(exp.getLength()) };

		return mScript.term("bv" + exp.getValue(), indices, null);
	}

	@Override
	public Term integerTranslation(final IntegerLiteral exp) {
		final BigInteger bigInt = new BigInteger(exp.getValue());
		final Rational rat = SmtUtils.toRational(bigInt);
		return rat.toTerm(SmtSortUtils.getIntSort(mScript));
	}

	@Override
	public Term realTranslation(final RealLiteral exp) {
		final Rational rat = SmtUtils.toRational(exp.getValue());
		return rat.toTerm(SmtSortUtils.getRealSort(mScript));
	}
}
