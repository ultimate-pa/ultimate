package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public abstract class BaseMemoryPointer implements IMemoryPointer {
	TypeSizes mTypeSizes;
	BoogieType mBoogieType;

	public BaseMemoryPointer(final TypeSizes typeSizes) {
		mTypeSizes = typeSizes;
	}

	/**
	 * Returns the base pointer Address.
	 *
	 * @return The base address.
	 */
	@Override
	public Expression pointerBaseAddress(final Expression pointer, final ILocation loc) {
		if (pointer instanceof StructConstructor) {
			return ((StructConstructor) pointer).getFieldValues()[0];
		}
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, SFO.POINTER_BASE);
	}
}
