package local.stalin.boogie.preprocessor;

import local.stalin.boogie.type.FunctionSignature;
import local.stalin.model.boogie.ast.FunctionDeclaration;

public class FunctionInfo {
	private final FunctionDeclaration declaration;
	private final String name;
	private final TypeParameters typeParams;
	private final FunctionSignature sig;
	
	public String getName() {
		return name;
	}

	public FunctionSignature getSignature() {
		return sig;
	}
	
	public TypeParameters getTypeParameters() {
		return typeParams;
	}

	public FunctionDeclaration getDeclaration() {
		return declaration;
	}
	
	public FunctionInfo(FunctionDeclaration declaration, String name, 
			TypeParameters typeParams, FunctionSignature sig) {
		this.declaration = declaration; 
		this.name = name;
		this.typeParams = typeParams;
		this.sig = sig;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(declaration.getIdentifier()).append(sig);
		return sb.toString();
	}
}
