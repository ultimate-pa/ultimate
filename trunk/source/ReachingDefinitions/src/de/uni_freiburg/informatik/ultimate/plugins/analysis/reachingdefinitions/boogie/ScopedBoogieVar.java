package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;

/***
 * Represents a unique Boogie variable based on its declaration.  
 * 
 * @author dietsch
 */
public class ScopedBoogieVar {

	private final VariableDeclaration mDeclaration;
	private final String mIdentifier;
	private final DeclarationInformation mDeclarationInformation;
	private final BoogieVar mBoogieVar;

	public ScopedBoogieVar(String identifier, VariableDeclaration declaration,
			DeclarationInformation declarationInformation, BoogieVar var) {
		mIdentifier = identifier;
		mDeclaration = declaration;
		mDeclarationInformation = declarationInformation;
		mBoogieVar = var;
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

	public BoogieVar getBoogieVar() {
		return mBoogieVar;
	}

	@Override
	public String toString() {
		return BoogiePrettyPrinter.print(getDeclaration());
	}

}
