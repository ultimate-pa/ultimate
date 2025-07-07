package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

/**
 * The memory model consisting of a MemoryAdressing and a MemoryStructure.
 */
public class MemoryModel {
	private final TypeSizes mTypeSizes;
	private final ITypeHandler mTypeHandler;

	private final IMemoryAdressing mMemoryAddressing;
	private final IMemoryStructure mMemoryStructure;

	public MemoryModel(final TranslationSettings settings, final TypeSizes typeSizes, final ITypeHandler typeHandler) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;

		mMemoryAddressing = MemoryModelFactory.createMemoryAddressing(settings);
		mMemoryStructure = MemoryModelFactory.createMemoryStructure(settings, mTypeSizes, mTypeHandler);
	}
}
