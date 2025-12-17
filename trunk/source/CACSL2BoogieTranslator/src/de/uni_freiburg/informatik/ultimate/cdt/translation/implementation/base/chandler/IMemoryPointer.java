/*
 * Copyright (C) 2025 Jan Körner
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

/**
 * Interface for memory pointer representations.
 *
 * This interface represents a memory pointer with operations for pointer creation, comparison, and retrieval of
 * pointer-related information within different memory addressing schemes.
 *
 * @author Jan Körner
 */
public interface IMemoryPointer {
	/**
	 * Returns the BoogieType that is used for a pointer.
	 *
	 * @return The type.
	 */
	BoogieType getPointerType();

	/**
	 * Creates a null pointer;
	 *
	 * @return The pointer.
	 */
	Expression constructNullPointer(final ILocation loc, final CPrimitive cTypeOfPointerComponent);

	/**
	 * Returns the type declaration.
	 *
	 * @return The declaration.
	 */
	TypeDeclaration getTypeDeclaration(final ILocation loc);

	/**
	 * Creates an initial pointer at certain value.
	 *
	 * @return The pointer.
	 */
	Expression constructInitialPointer(final ILocation loc, final BigInteger value,
			final CPrimitive cTypeOfPointerComponent);

	/**
	 * Returns the base pointer Address.
	 *
	 * @return The base address.
	 */
	Expression getPointerAddress(final Expression pointer, final ILocation loc);

	/**
	 * Creates the expression used for the pointer relation.
	 *
	 * @return The expression.
	 */
	Expression constructPointerRelationExpression(final ILocation loc, final Expression baseEquality,
			final CheckMode mPointerSubtractionAndComparisonValidityCheckMode,
			final ExpressionTranslation expressionTranslation, final int op, final ExpressionResult leftPointer,
			final ExpressionResult rightPointer);

	/**
	 * Constructs a pointer component relation. For 1D-pointer only base is valid for 2D-pointer base, and offset are
	 * valid. Construct {@link Expression} that compares a component of two pointers.
	 *
	 * @return The expression.
	 */
	Expression constructPointerComponentRelation(final ILocation loc, final int op, final Expression leftPointer,
			final Expression rightPointer, final String component, ExpressionTranslation expressionTranslation);

	/**
	 * Checks if a given Expression is a null pointer.
	 *
	 * @return If it's a null pointer.
	 */
	boolean isNullPointer(final Expression ptr);
}
