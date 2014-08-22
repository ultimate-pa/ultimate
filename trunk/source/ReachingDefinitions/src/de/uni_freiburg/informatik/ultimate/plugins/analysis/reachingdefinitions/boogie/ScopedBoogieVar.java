package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

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

	public ScopedBoogieVar(IdentifierExpression identifier, BoogieSymbolTable symbolTable) {
		this(identifier.getIdentifier(), (VariableDeclaration) symbolTable.getDeclaration(identifier), identifier
				.getDeclarationInformation());
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

}
