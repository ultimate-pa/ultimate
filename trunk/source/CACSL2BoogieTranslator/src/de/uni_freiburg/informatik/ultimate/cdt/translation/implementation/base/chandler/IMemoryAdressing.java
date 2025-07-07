package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;

/**
 * The interface defining the functions for the different addressing modes.
 */
public interface IMemoryAdressing {
	/**
	 * Constructs the required metadata for the selected addressing mode.
	 *
	 * @param requiredFeatures
	 *            The Features that are currently needed for the program to be verified.
	 * @return The metadata declarations.
	 */
	List<Declaration> constructMetaData(RequiredMemoryModelFeatures requiredFeatures);

	/**
	 * Returns a list of metadata declarations needed for the memory model infrastructure.
	 *
	 * @return The declarations.
	 */
	List<MemoryModelDeclarations> metaDataDeclarations();
}
