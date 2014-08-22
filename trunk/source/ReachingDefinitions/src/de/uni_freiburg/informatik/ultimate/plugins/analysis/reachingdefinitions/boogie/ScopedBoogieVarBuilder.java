package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class ScopedBoogieVarBuilder {

	private final BoogieSymbolTable mSymbolTable;

	public ScopedBoogieVarBuilder(BoogieSymbolTable table) {
		mSymbolTable = table;
	}

	public ScopedBoogieVar getScopedBoogieVar(VariableLHS lhs) {
		return new ScopedBoogieVar(lhs.getIdentifier(), (VariableDeclaration) mSymbolTable.getDeclaration(lhs
				.getIdentifier(), lhs.getDeclarationInformation().getStorageClass(), lhs.getDeclarationInformation()
				.getProcedure()), lhs.getDeclarationInformation());
	}

	public ScopedBoogieVar getScopedBoogieVar(IdentifierExpression identifier) {
		return new ScopedBoogieVar(identifier, mSymbolTable);
	}

}
