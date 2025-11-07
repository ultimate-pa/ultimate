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
