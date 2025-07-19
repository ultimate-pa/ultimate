package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;

public abstract class BaseMemoryPointer implements IMemoryPointer {
	TypeSizes mTypeSizes;
	BoogieType mBoogieType;

	public BaseMemoryPointer(final TypeSizes typeSizes) {
		mTypeSizes = typeSizes;
	}
}
