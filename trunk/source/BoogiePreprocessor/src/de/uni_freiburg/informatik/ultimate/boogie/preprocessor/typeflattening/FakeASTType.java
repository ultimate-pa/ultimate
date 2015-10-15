package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Placeholder AST Type for type declarations during type flattening
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class FakeASTType extends ASTType {
	private static final long serialVersionUID = 9122128920903038040L;

	public FakeASTType(ILocation loc) {
		super(loc);
	}
}