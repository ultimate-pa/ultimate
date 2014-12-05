package de.uni_freiburg.informatik.ultimate.astbuilder;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

/**
 * Emitter for the ACSL AST.
 * 
 * @author Markus Lindenmann
 * @since 10.12.2012
 */
public class ACSLEmit extends Emit {

	private static final String sVisitorName = "ACSLVisitor";
	private static final String sTransformerName = "ACSLTransformer";
	private static final String[] sOthers = new String[] { sVisitorName, sTransformerName };

	private boolean isOther(Node node) {
		for (String s : sOthers) {
			if (node.getName().equals(s)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void emitClassDeclaration(Node node) throws IOException {
		StringBuilder classDecl = new StringBuilder();
		classDecl.append("public ");
		if (node.isAbstract()) {
			classDecl.append("abstract ");
		}
		classDecl.append("class ");
		classDecl.append(node.getName());

		if (node.getParent() != null) {
			classDecl.append(" extends ");
			classDecl.append(node.getParent().getName());
		} else if (!isOther(node)) {
			classDecl.append(" extends ACSLNode");
		}

		if (node.getInterfaces() != null) {
			classDecl.append(" implements ");
			classDecl.append(node.getInterfaces());
		}
		classDecl.append(" {");
		mWriter.println(classDecl.toString());
	}

	@Override
	public void emitPreamble(Node node) throws IOException {
		super.emitPreamble(node);
		if (!isOther(node)) {
			mWriter.println("import java.util.List;");
			if (node.getParent() == null) {
				mWriter.println("import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;");
			}

			for (Parameter p : getAllACSLParameters(node)) {
				if (isArrayType(p)) {
					mWriter.println("import java.util.ArrayList;");
					break;
				}
			}
		}
	}

	@Override
	public void emitNodeHook(Node node) throws IOException {
		if (node.name.equals(sVisitorName)) {
			for (Node n : mGrammar.getNodeTable().values()) {
				mWriter.println();
				mWriter.println("    public boolean visit(" + n.name + " node) {");
				mWriter.println("        return true;");
				mWriter.println("    }");
			}

		} else if (node.name.equals(sTransformerName)) {
			for (Node n : mGrammar.getNodeTable().values()) {
				mWriter.println();
				mWriter.println("    public " + n.name + " transform(" + n.name + " node) {");
				mWriter.println("        return node;");
				mWriter.println("    }");
			}

		} else {
			mWriter.println();
			mWriter.println("    public List<Object> getChildren() {");
			mWriter.println("        List<Object> children = super.getChildren();");
			Parameter[] parameters = node.getParameters();
			for (int i = 0; i < parameters.length; i++) {
				mWriter.println("        children.add(" + parameters[i].getName() + ");");
			}
			mWriter.println("        return children;");
			mWriter.println("    }");

			if (!node.isAbstract()) {
				List<Parameter> allACSLParameters = getAllACSLParameters(node);
				writeVisitorAcceptMethod(node, allACSLParameters);
				writeTransformerAcceptMethod(node, allACSLParameters);

			} else {
				mWriter.println();
				mWriter.println("    public abstract void accept(" + sVisitorName + " visitor);");

				mWriter.println();
				mWriter.println("    public abstract " + node.name + " accept(" + sTransformerName + " visitor);");
			}

		}
	}

	private void writeTransformerAcceptMethod(Node node, List<Parameter> allACSLParameters) {
		// accept method for transformer
		mWriter.println();
		mWriter.println("    public " + node.name + " accept(" + sTransformerName + " visitor) {");
		mWriter.println("        " + node.name + " node = visitor.transform(this);");
		mWriter.println("        if(node != this){");
		mWriter.println("            return node;");
		mWriter.println("        }");
		mWriter.println();

		boolean isChangedPrinted = false;

		for (Parameter p : allACSLParameters) {
			String newName = "new" + p.getName();
			String listName = "tmpList" + newName;
			// declarations
			if (isArrayType(p)) {
				if (!isChangedPrinted) {
					mWriter.println("        boolean isChanged=false;");
					isChangedPrinted = true;
				}
				mWriter.println("            ArrayList<" + getBaseType(p) + "> " + listName + " = new ArrayList<>();");
			} else {
				mWriter.println("            " + p.type + " " + newName + " = null;");
			}

			mWriter.println("        if(" + p.getName() + " != null){");
			if (isArrayType(p)) {
				mWriter.println("            for(" + getBaseType(p) + " elem : " + p.getName() + "){");
				mWriter.println("                " + getBaseType(p) + " " + newName + " = elem.accept(visitor);");
				mWriter.println("                isChanged = isChanged || " + newName + " != elem;");
				mWriter.println("                " + listName + ".add(elem.accept(visitor));");
				mWriter.println("            }");
			} else {
				mWriter.println("            " + newName + " = " + p.getName() + ".accept(visitor);");
			}
			mWriter.println("        }");
		}

		if (allACSLParameters.size() > 0) {

			StringBuilder sb = new StringBuilder();
			sb.append("        if(");

			if (isChangedPrinted) {
				sb.append("isChanged || ");
			}

			for (Parameter p : allACSLParameters) {
				if (isArrayType(p)) {
					continue;
				}
				String newName = "new" + p.getName();
				sb.append(p.name + " != " + newName);
				sb.append(" || ");
			}
			if (sb.substring(sb.length() - 4, sb.length()).equals(" || ")) {
				sb.delete(sb.length() - 4, sb.length());
			}
			sb.append("){");
			mWriter.println(sb.toString());
			mWriter.println("            return new " + node.name + "(" + getNewCallParams(node) + ");");
			mWriter.println("        }");
		}
		mWriter.println("        return this;");
		mWriter.println("    }");
	}

	private boolean isArrayType(Parameter p) {
		if (p.getType().contains("[]")) {
			return true;
		}
		return false;
	}

	private String getBaseType(Parameter p) {
		String typeStr = p.getType().replaceAll("\\[\\]", "");
		return typeStr;
	}

	private String getNewCallParams(Node node) {
		if (node == null) {
			return "";
		}

		StringBuffer sb = new StringBuffer();

		sb.append(getNewCallParams(node.getParent()));

		String comma = "";
		if (sb.length() > 0)
			comma = ", ";

		for (Parameter p : node.getParameters()) {
			String pname;
			if (!mGrammar.nodeTable.containsKey(getBaseType(p))) {
				pname = p.getName();
			} else if (isArrayType(p)) {
				pname = "tmpListnew" + p.getName() + ".toArray(new " + getBaseType(p) + "[0])";
			} else {
				pname = "new" + p.getName();
			}
			sb.append(comma).append(pname);
			comma = ", ";
		}
		return sb.toString();

	}

	private void writeVisitorAcceptMethod(Node node, List<Parameter> allACSLParameters) {
		// accept method for visitor
		mWriter.println();
		mWriter.println("    public void accept(" + sVisitorName + " visitor) {");

		String lineSep = System.getProperty("line.separator");

		Node parent = node.getParent();
		String indent = "        ";
		int i = 0;
		StringBuilder sb = new StringBuilder();
		if (parent != null) {
			while (parent != null) {
				int j = i + 1;
				while (j > 0) {
					sb.append(indent);
					j--;
				}
				sb.append("if(visitor.visit((" + parent.name + ")this)){");
				sb.append(lineSep);
				parent = parent.getParent();
				i++;
			}

			while (i > 0) {
				int j = i + 1;
				String localIndent = "";
				while (j > 0) {
					localIndent = localIndent + indent;
					j--;
				}
				sb.append(localIndent);
				sb.append("} else {");
				sb.append(lineSep);
				sb.append(indent);
				sb.append(localIndent);
				sb.append("return;");
				sb.append(lineSep);
				sb.append(localIndent);
				i--;
			}
			sb.append(indent);
			sb.append("}");
			mWriter.println(sb.toString());
		}

		mWriter.println("        if(visitor.visit(this)){");
		for (Parameter p : allACSLParameters) {
			mWriter.println("            if(" + p.getName() + "!=null){");
			if (isArrayType(p)) {
				mWriter.println("                for(" + getBaseType(p) + " elem : " + p.getName() + "){");
				mWriter.println("                    elem.accept(visitor);");
				mWriter.println("                }");

			} else {
				mWriter.println("                " + p.getName() + ".accept(visitor);");
			}
			mWriter.println("            }");
		}
		mWriter.println("        }");
		mWriter.println("    }");
	}

	private List<Parameter> getAllACSLParameters(Node node) {
		List<Parameter> allParameters = new ArrayList<>();
		Node current = node;
		while (current != null) {
			for (Parameter p : current.getParameters()) {
				if (mGrammar.nodeTable.containsKey(getBaseType(p))) {
					allParameters.add(p);
				}
			}
			current = current.getParent();
		}
		return allParameters;
	}

	@Override
	public void setGrammar(Grammar grammar) {
		HashSet<String> types = new HashSet<>();
		for (Node n : grammar.getNodeTable().values()) {
			types.add(n.name);
		}
		grammar.getNodeTable()
				.put(sVisitorName, new Node(sVisitorName, null, null, "", types, false, new Parameter[0]));
		grammar.getNodeTable().put(sTransformerName,
				new Node(sTransformerName, null, null, "", types, false, new Parameter[0]));
		super.setGrammar(grammar);
	}
}
