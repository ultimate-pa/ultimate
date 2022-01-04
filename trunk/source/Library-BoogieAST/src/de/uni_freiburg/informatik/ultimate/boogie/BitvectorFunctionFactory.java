/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BitvectorConstantOperationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.SupportedBitvectorOperations;

/**
 * Boogie does not provide native support for most bitvector operations of
 * SMT-LIB. These operations are however very helpful for modeling C programs.
 * Hence we developed a convention based on the :smtdefined attibute that allows
 * us to give Boogie functions the semantics of SMT-LIB functions.
 * {@link https://github.com/ultimate-pa/ultimate/wiki/Boogie#attribute-defined-directives}
 * Unfortunately, this was not sufficient. We also have to be able to
 * translate SMT functions back to Boogie functions. Because of that
 * we want to have a uniform construction for all function declarations
 * and all function calls. This class provides these constructions.
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BitvectorFunctionFactory {

	public static final String AUXILIARY_FUNCTION_PREFIX = "~";

	public static String generateBoogieFunctionName(final SupportedBitvectorOperations bvop, final int bitsize) {
		if (bitsize <= 0) {
			throw new IllegalArgumentException();
		}
		switch (bvop) {
		case bvadd:
		case bvand:
		case bvashr:
		case bvlshr:
		case bvmul:
		case bvneg:
		case bvnot:
		case bvor:
		case bvsdiv:
		case bvsge:
		case bvsgt:
		case bvshl:
		case bvsle:
		case bvslt:
		case bvsmod:
		case bvsrem:
		case bvsub:
		case bvudiv:
		case bvuge:
		case bvugt:
		case bvule:
		case bvult:
		case bvurem:
		case bvxor:
			return AUXILIARY_FUNCTION_PREFIX + bvop.toString() + bitsize;
		case concat:
		case extract:
			throw new IllegalArgumentException("Boogie has native support for this operation.");
		case sign_extend:
		case zero_extend:
			throw new IllegalArgumentException("Call method for extend.");
		default:
			throw new AssertionError("unknown value " + bvop);
		}
	}

	public static Expression constructInequalityFunction(final ILocation loc, final Expression exp1,
			final Expression exp2, final SupportedBitvectorOperations bvop, final int bitsize) {
		final String boogieFunctionName = generateBoogieFunctionName(bvop, bitsize);
		final Expression result = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
				new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
		return result;
	}

	public static Expression constructUnaryOperation(final ILocation loc, final SupportedBitvectorOperations bvop,
			final Expression expr) {
		if (expr instanceof BitvecLiteral) {
			final BitvectorConstant bc = ExpressionFactory.toConstant((BitvecLiteral) expr);
			final BitvectorConstantOperationResult resBc = BitvectorConstant.apply(bvop, bc);
			return ExpressionFactory.toBitvectorLiteral(loc, resBc.getBvResult());
		} else {
			final String boogieFunctionName = generateBoogieFunctionName(bvop,
					ExpressionFactory.isBitvectorSort(expr.getType()));
			final Expression func = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { expr }, (BoogieType) expr.getType());
			return func;
		}
	}

	public static Expression constructBinaryOperation(final ILocation loc, final SupportedBitvectorOperations bvop,
			final Expression... exprs ) {
		if (exprs.length <= 1) {
			throw new IllegalArgumentException("not binary");
		}
		final String boogieFunctionName = generateBoogieFunctionName(bvop,
				ExpressionFactory.isBitvectorSort(exprs[0].getType()));
		Expression result = exprs[0];
		for (int i = 1; i < exprs.length; i++) {
			result = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { result, exprs[i] }, (BoogieType) exprs[0].getType());
		}
		return result;
	}

}
