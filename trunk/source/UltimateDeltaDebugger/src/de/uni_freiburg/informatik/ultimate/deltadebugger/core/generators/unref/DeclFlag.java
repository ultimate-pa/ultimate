package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

/**
 * Specifies what kind of unreferenced declarations to delete. All flags can be combined.
 */
public enum DeclFlag {
	// The type of declarations to consider: Typedefs or variables (i.e. not typedefs).
	TYPEDEFS, VARS, 
	// The scope where declarations are considered
	GLOBAL, LOCAL, MEMBERS, 
	// Optionally delete leading macros together with the full declaration
	INCLUDE_EMPTY_MACROS, INCLUDE_EXTENSION_MACRO
}
