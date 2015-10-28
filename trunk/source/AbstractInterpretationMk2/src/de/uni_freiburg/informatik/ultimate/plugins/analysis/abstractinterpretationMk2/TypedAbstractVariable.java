package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

/**
 * @author GROSS-JAN
 *
 */
public class TypedAbstractVariable extends AbstractVariable {
	private final DeclarationInformation mDeclaration;
	private final IType mType;

	/**
	 * Create an abstract variable with type and declaration information
	 */
	public TypedAbstractVariable(String ident,
			DeclarationInformation declaration, IType type) {
		super(ident);
		mDeclaration = declaration;
		mType = type;
	}

	public IType getType() {
		return mType;
	}

	public DeclarationInformation getDeclaration() {
		return mDeclaration;
	}

	@Override
	public String toString() {
		String s = super.toString();
		// if(mDeclaration != null)
		// {
		// s += "+".concat(mDeclaration.toString());
		// }
		// if(mType != null)
		// {
		// s += ":".concat(mType.toString());
		// }

		return s;
	}
}
