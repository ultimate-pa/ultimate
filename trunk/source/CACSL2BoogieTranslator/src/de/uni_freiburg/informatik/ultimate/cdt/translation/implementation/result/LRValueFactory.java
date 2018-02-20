package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

public class LRValueFactory {

	public static HeapLValue constructHeapLValue(final Dispatcher main, final Expression address, final CType cType,
			final BitfieldInformation bi) {
		assert address.getType().equals(main.mTypeHandler.getBoogiePointerType());
		return new HeapLValue(address, cType, bi);
	}

	public static HeapLValue constructHeapLValue(final Dispatcher main, final Expression address, final CType cType,
			final boolean isIntFromPtr, final BitfieldInformation bi) {
		assert address.getType().equals(main.mTypeHandler.getBoogiePointerType());
		return new HeapLValue(address, cType, isIntFromPtr, bi);
	}
}
