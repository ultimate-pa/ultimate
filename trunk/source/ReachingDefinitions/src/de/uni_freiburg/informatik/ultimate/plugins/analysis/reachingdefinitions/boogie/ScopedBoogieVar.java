package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;

/***
 * 
 * Represents a unique Boogie variable
 * 
 * @author dietsch
 * 
 */
public class ScopedBoogieVar {

	private final VariableDeclaration mDeclaration;
	private final String mIdentifier;
	private final DeclarationInformation mDeclarationInformation;

	public ScopedBoogieVar(String identifier, VariableDeclaration declaration,
			DeclarationInformation declarationInformation) {
		mIdentifier = identifier;
		mDeclaration = declaration;
		mDeclarationInformation = declarationInformation;
	}

	public VariableDeclaration getDeclaration() {
		return mDeclaration;
	}

	public String getIdentifier() {
		return mIdentifier;
	}

	public DeclarationInformation getDeclarationInformation() {
		return mDeclarationInformation;
	}

	@Override
	public String toString() {
		return BoogieStatementPrettyPrinter.print(getDeclaration());
	}

}
