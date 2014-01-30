package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

public class ResultDeclaration extends Result {

	ArrayList<CDeclaration> mDecls = new ArrayList<CDeclaration>();
	
	public ResultDeclaration() {
		super(null);
	}
	
	public void addDeclaration(CType type, String name, ResultExpression initializer, boolean onHeap) {
		mDecls.add(new CDeclaration(type, name, initializer, onHeap));
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
