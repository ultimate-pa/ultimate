package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import javax.management.RuntimeErrorException;

import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

public class AbstractVariable {
	private final String mIdentifier;
	private final DeclarationInformation mDeclaration;

	public AbstractVariable(String str,
			DeclarationInformation declaration) {
		if(declaration == null)
		{
			throw new Error("ASDF");
		}
		mIdentifier = str;
		mDeclaration = declaration;		
	}

	public String getString() {
		return mIdentifier;
	}

	@Override
	public String toString() {
		return mIdentifier.toString();
	}

	public DeclarationInformation getDeclaration() {
		return mDeclaration;
	}
	
	// TODO: hashCode() and equals() are not implemented correctly, but this
	// domain hinges on this incorrect implementation.

	@Override
	public int hashCode() {
		return mIdentifier.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || !(obj instanceof AbstractVariable)) {
			return false;
		}
		AbstractVariable other = (AbstractVariable) obj;
		return mIdentifier.equals(other.mIdentifier) &&
				mDeclaration.equals(other.mDeclaration);
	}
}
