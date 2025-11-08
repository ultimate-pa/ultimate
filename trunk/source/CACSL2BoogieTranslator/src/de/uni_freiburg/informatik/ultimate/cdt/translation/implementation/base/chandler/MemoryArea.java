package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

public enum MemoryArea {
	STACK, HEAP;

	MemoryModelDeclarations getMemoryStructureDeclaration() {
		return switch (this) {
		case HEAP -> MemoryModelDeclarations.ULTIMATE_ALLOC_HEAP;
		case STACK -> MemoryModelDeclarations.ULTIMATE_ALLOC_STACK;
		};
	}
}
