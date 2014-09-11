package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTInitializer;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

/**
 * A Result that contains CDeclarations.
 * It is used in the visitor pattern for returning one or more of those.
 * The dispatch of a CASTDeclarator yields a ResultDeclaration with only one CDeclaration inside.
 * ResultDeclaration has to be able to hold several CDeclarations because it is also used as a Result
 * of a CASTSimpleDeclaration -- which may contain several Declarators.  
 */
public class ResultDeclaration extends Result {

	ArrayList<CDeclaration> mDecls = new ArrayList<CDeclaration>();
	
	public ResultDeclaration() {
		super(null);
	}
	
//	public void addDeclaration(CType type, String name, ResultExpression initializer, boolean onHeap) {
	public void addDeclaration(CType type, String name, IASTInitializer cAstInitializer, ResultExpression initializer, boolean onHeap) {
		mDecls.add(new CDeclaration(type, name, cAstInitializer, initializer, onHeap));
	}

	public void addDeclaration(CDeclaration decl) {
		mDecls.add(decl);
	}
	
	public void addDeclarations(List<CDeclaration> decls) {
		mDecls.addAll(decls);
	}
	
	public List<CDeclaration> getDeclarations() {
		return mDecls;
	}
	
	public String toString() {
		return mDecls.toString();
	}
}
