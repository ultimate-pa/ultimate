package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;

public class PRSymbolTableValue extends SymbolTableValue {

	public PRSymbolTableValue(String bId, Declaration boogieDecl,
			CDeclaration cdecl, boolean isGlobal, StorageClass sc, IASTNode decl) {
		super(bId, boogieDecl, cdecl, isGlobal, sc);
		this.decl = decl;
	}
	
	public IASTNode decl;

}
