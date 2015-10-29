package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

/**
 * @author Jan Hättig
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
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((mDeclaration == null) ? 0 : mDeclaration.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		TypedAbstractVariable other = (TypedAbstractVariable) obj;
		if (mDeclaration == null) {
			if (other.mDeclaration != null)
				return false;
		} else if (!mDeclaration.equals(other.mDeclaration))
			return false;
		return true;
	}
}
