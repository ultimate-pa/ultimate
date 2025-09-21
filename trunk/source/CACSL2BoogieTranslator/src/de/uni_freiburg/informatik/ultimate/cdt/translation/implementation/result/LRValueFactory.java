package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

public class LRValueFactory {

	public static HeapLValue constructHeapLValue(final ITypeHandler typehandler, final Expression address,
			final ICType cType, final BitfieldInformation bi) {
		assert address.getType().equals(typehandler.getBoogiePointerType());
		return new HeapLValue(address, cType, bi);
	}

	public static HeapLValue constructHeapLValue(final ITypeHandler typehandler, final Expression address,
			final ICType cType, final boolean isIntFromPtr, final BitfieldInformation bi) {
		assert address.getType().equals(typehandler.getBoogiePointerType());
		return new HeapLValue(address, cType, isIntFromPtr, bi);
	}
}
