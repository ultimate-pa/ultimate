package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

/**
 * Specifies what kind of unreferenced objects to delete. All flags can be combined.
 */
public enum ObjFlag {
	// The type of definitions to consider
	FUNCDEFS, PROTOTYPES, COMPOSITES, ENUMS, 
	// Optionally delete leading macros together with the full declaration
	INCLUDE_ACSLCOMMENT, INCLUDE_EMPTY_MACROS, INCLUDE_EXTENSION_MACRO
}
