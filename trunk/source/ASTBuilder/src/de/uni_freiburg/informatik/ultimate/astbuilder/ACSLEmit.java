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
		} else if (!node.getName().equals(sVisitorName)) {
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
		if (!node.name.equals(sVisitorName)) {
			mWriter.println("import java.util.List;");
			if (node.getParent() == null) {
				mWriter.println("import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;");
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
				List<Parameter> allParameters = new ArrayList<>();
				Node current = node;
				while (current != null) {
					for (Parameter p : current.getParameters()) {
						if (mGrammar.nodeTable.containsKey(p.getType())) {
							allParameters.add(p);
						}
					}
					current = current.getParent();
				}

				mWriter.println();
				mWriter.println("    public void accept(" + sVisitorName + " visitor) {");
				mWriter.println("        if(visitor.visit(this)){");
				for (Parameter p : allParameters) {
					mWriter.println("            if(" + p.getName() + "!=null){");
					mWriter.println("                " + p.getName() + ".accept(visitor);");
					mWriter.println("            }");
				}
				mWriter.println("        }");
				mWriter.println("    }");
			} else {
				mWriter.println();
				mWriter.println("    public abstract void accept(" + sVisitorName + " visitor);");
			}

		}
	}

	@Override
	public void setGrammar(Grammar grammar) {
		HashSet<String> types = new HashSet<>();
		for (Node n : grammar.getNodeTable().values()) {
			types.add(n.name);
		}
		Node visitorNode = new Node(sVisitorName, null, null, "", types, false, new Parameter[0]);
		grammar.getNodeTable().put(sVisitorName, visitorNode);
		super.setGrammar(grammar);
	}
}
