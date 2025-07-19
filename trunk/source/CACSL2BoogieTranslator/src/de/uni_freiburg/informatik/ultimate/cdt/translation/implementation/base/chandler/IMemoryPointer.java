package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public interface IMemoryPointer {
	/**
	 * Returns the BoogieType that is used for a pointer.
	 *
	 * @return The type.
	 */
	BoogieType pointerType();

	/**
	 * Creates a null pointer;
	 *
	 * @return The pointer.
	 */
	Expression nullPointer(final ILocation loc, final CPrimitive cTypeOfPointerComponent);

	/**
	 * Returns the type declaration.
	 *
	 * @return The declaration.
	 */
	TypeDeclaration typeDeclaration(final ILocation loc);

	/**
	 * Creates an initial pointer at certain value.
	 *
	 * @return The pointer.
	 */
	Expression initialPointer(final ILocation loc, final BigInteger value, final CPrimitive cTypeOfPointerComponent);
}
