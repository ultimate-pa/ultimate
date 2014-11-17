package de.uni_freiburg.informatik.ultimate.astbuilder;

import java.io.IOException;

public class NewUltimateEmit extends Emit {
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.astbuilder.Emit#emitClassDeclaration
	 * (de.uni_freiburg.informatik.ultimate.astbuilder.Node)
	 */
	// @Override
	public void emitClassDeclaration(Node node) throws IOException {
		mWriter.println("public " + (node.isAbstract() ? "abstract " : "") + "class " + node.getName()
				+ (node.getParent() != null ? " extends " + node.getParent().getName() : " extends BoogieASTNode")
				+ (node.getInterfaces() != null ? " implements " + node.getInterfaces() : "") + " {");
		formatComment(mWriter, "    ", "The serial version UID.");
		mWriter.println("    private static final long serialVersionUID = 1L;");
	}

	public String getConstructorParam(Node node, boolean optional) {
		if (node == null)
			return "loc";
		return super.getConstructorParam(node, optional);
	}

	protected void fillConstructorParamComment(Node node, StringBuffer param, StringBuffer comment, boolean optional) {
		if (node.getParent() == null) {
			param.append("ILocation loc");
			comment.append("\n@param loc the node's location");
		}
		super.fillConstructorParamComment(node, param, comment, optional);
	}

	public void emitConstructors(Node node) throws IOException {
		int numNotWriteableParams = 1;
		int numNotOptionalParams = 1;
		int numTotalParams = 1;

		/* Default constructor is only emitted if all fields are writeable */
		/* Optional constructor is only emitted if there are optional fields */
		Node ancestor = node;
		while (ancestor != null) {
			for (Parameter p : ancestor.parameters) {
				numTotalParams++;
				if (!p.isWriteable())
					numNotWriteableParams++;
				if (!p.isOptional())
					numNotOptionalParams++;
			}
			ancestor = ancestor.getParent();
		}
		if (numNotOptionalParams == 0 || numNotWriteableParams == 0) {
			formatComment(mWriter, "    ", "The default constructor.");
			mWriter.println("    public " + node.getName() + "() {");
			mWriter.println("    }");
			mWriter.println();
		}

		if (numNotOptionalParams > 0 && numNotOptionalParams < numTotalParams)
			emitConstructor(node, false);
		if (numTotalParams > 0)
			emitConstructor(node, true);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.astbuilder.Emit#emitPreamble(de.
	 * uni_freiburg.informatik.ultimate.astbuilder.Node)
	 */
	// @Override
	public void emitPreamble(Node node) throws IOException {
		super.emitPreamble(node);
		mWriter.println("import java.util.List;");
		mWriter.println("import de.uni_freiburg.informatik.ultimate.model.location.ILocation;");
		mWriter.println("import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;");
		if (needsArraysPackage(node)) {
			mWriter.println("import java.util.Arrays;");
		}
	}

	public void emitNodeHook(Node node) throws IOException {
		mWriter.println();
		mWriter.println("    public List<BoogieASTNode> getOutgoingNodes() {");
		mWriter.println("        List<BoogieASTNode> children = super.getOutgoingNodes();");
		Parameter[] parameters = node.getParameters();
		System.out.println(node.getName() + " has " + parameters.length + " parameters");
		for (int i = 0; i < parameters.length; i++) {

			if (isNoRegularChild(parameters[i].getType())) {
				continue;
			}
			System.out.println(parameters[i].getName() + " is an array? " + isArray(parameters[i].getType()));
			
			if (isArray(parameters[i].getType())) {
				mWriter.println(String.format("        if(%s!=null){", parameters[i].getName()));
				mWriter.println(String.format("            children.addAll(Arrays.asList(%s));", parameters[i].getName()));
				mWriter.println("        }");
			} else {
				mWriter.println("        children.add(" + parameters[i].getName() + ");");
			}
		}
		mWriter.println("        return children;");
		mWriter.println("    }");
	}

	private boolean isNoRegularChild(String type) {
		while (type.endsWith("[]"))
			type = type.substring(0, type.length() - 2);
		return !(mGrammar.getNodeTable().containsKey(type));
	}

	private boolean needsArraysPackage(Node node) {
		for (Parameter s : node.getParameters()) {
			
			if(isNoRegularChild(s.getType())){
				continue;
			}
			
			if (isArray(s.getType())) {
				return true;
			}
		}
		return false;
	}

	private boolean isArray(String type) {
		return type.contains("[");
	}

}
