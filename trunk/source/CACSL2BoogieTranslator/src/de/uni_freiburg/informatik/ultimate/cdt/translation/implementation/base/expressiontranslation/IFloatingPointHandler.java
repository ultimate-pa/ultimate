/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Handles expressions representing floating point operations according to the IEEE standard 754-2008.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public interface IFloatingPointHandler {
	/**
	 * Returns an expression representing {@code argument} rounded to an integer according to the given
	 * {@code roundingMode}.
	 */
	Expression roundToIntegral(ILocation loc, Expression argument, CPrimitive type, Expression roundingMode);

	/**
	 * Returns an expression representing the square root of {@code argument}.
	 */
	Expression sqrt(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression representing the absolute value of {@code argument}.
	 */
	Expression abs(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression that checks if {@code argument} is NaN (not a number).
	 */
	Expression isNan(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression that checks if {@code argument} is infinite (i.e., either plus or minus infinity).
	 */
	Expression isInfinite(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression that checks if {@code argument} is a normal number (see IEEE 754-2008 2.1.38: "a finite
	 * non-zero floating-point number with magnitude greater than or equal to a minimum b^emin value, where b is the
	 * radix").
	 */
	Expression isNormal(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression that checks if {@code argument} is zero (i.e., either plus or minus zero).
	 */
	Expression isZero(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression that checks if {@code argument} is a subnormal number (see IEEE 754-2008 2.1.51: "a
	 * non-zero floating-point number with magnitude less than the magnitude of that format's smallest normal number").
	 */
	Expression isSubnormal(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Returns an expression that checks if {@code argument} is positive (incl. plus zero).
	 */
	Expression isPositive(ILocation loc, Expression argument, CPrimitive type);

	/**
	 * Create an expression representing NaN (not a number).
	 */
	Expression createNan(ILocation loc, CPrimitive type);

	/**
	 * Create an expression representing plus infinity.
	 */
	Expression createInfinity(ILocation loc, CPrimitive type);

	/**
	 * Create an expression representing minus infinity.
	 */
	Expression createMinusInfinity(ILocation loc, CPrimitive type);

	/**
	 * Create an expression representing plus zero.
	 */
	Expression createPlusZero(ILocation loc, CPrimitive type);

	/**
	 * Returns an expression representing the minimum of {@code firstArgument} and {@code secondArgument}.
	 */
	Expression min(ILocation loc, Expression firstArgument, Expression secondArgument, CPrimitive type);

	/**
	 * Returns an expression representing the maximum of {@code firstArgument} and {@code secondArgument}.
	 */
	Expression max(ILocation loc, Expression firstArgument, Expression secondArgument, CPrimitive type);

	/**
	 * Returns an expression representing the remainder of {@code firstArgument} divided by {@code secondArgument} (see
	 * IEEE 754-2008 5.3.1: "When y ≠ 0, the remainder r = remainder(x, y) is defined for finite x and y regardless of
	 * the rounding-direction attribute by the mathematical relation r = x − y × n, where n is the integer nearest the
	 * exact number x/y ; whenever | n − x/y | = ½ , then n is even. Thus, the remainder is always exact. If r = 0, its
	 * sign shall be that of x. remainder(x, ∞) is x for finite x.").
	 */
	Expression remainder(ILocation loc, Expression firstArgument, Expression secondArgument, CPrimitive type);
}
