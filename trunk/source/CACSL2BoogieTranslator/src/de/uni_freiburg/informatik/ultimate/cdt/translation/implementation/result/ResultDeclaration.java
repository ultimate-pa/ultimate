package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTInitializer;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

public class ResultDeclaration extends Result {

	ArrayList<CDeclaration> mDecls = new ArrayList<CDeclaration>();
	
	public ResultDeclaration() {
		super(null);
	}
	
//	public void addDeclaration(CType type, String name, ResultExpression initializer, boolean onHeap) {
	public void addDeclaration(CType type, String name, IASTInitializer cAstInitializer, boolean onHeap) {
		mDecls.add(new CDeclaration(type, name, cAstInitializer, onHeap));
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
