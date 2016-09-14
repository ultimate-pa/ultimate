/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ASTBuilder plug-in.
 * 
 * The ULTIMATE ASTBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ASTBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ASTBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ASTBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ASTBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
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

	private boolean isOther(final Node node) {
		for (final String s : sOthers) {
			if (node.getName().equals(s)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void emitClassDeclaration(final Node node) throws IOException {
		final StringBuilder classDecl = new StringBuilder();
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
	public void emitPreamble(final Node node) throws IOException {
		super.emitPreamble(node);
		if (!isOther(node)) {
			mWriter.println("import java.util.List;");
			if (node.getParent() == null) {
				mWriter.println("import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;");
			}

			for (final Parameter p : getAllACSLParameters(node)) {
				if (isArrayType(p)) {
					mWriter.println("import java.util.ArrayList;");
					break;
				}
			}
		}
	}

	@Override
	public void emitNodeHook(final Node node) throws IOException {
		if (node.name.equals(sVisitorName)) {
			for (final Node n : mGrammar.getNodeTable().values()) {
				mWriter.println();
				mWriter.println("    public boolean visit(" + n.name + " node) {");
				mWriter.println("        return true;");
				mWriter.println("    }");
			}

		} else if (node.name.equals(sTransformerName)) {
			for (final Node n : mGrammar.getNodeTable().values()) {
				mWriter.println();
				mWriter.println("    public " + n.name + " transform(" + n.name + " node) {");
				mWriter.println("        return node;");
				mWriter.println("    }");
			}

		} else {
			mWriter.println();
			mWriter.println("    public List<Object> getChildren() {");
			mWriter.println("        List<Object> children = super.getChildren();");
			final Parameter[] parameters = node.getParameters();
			for (int i = 0; i < parameters.length; i++) {
				mWriter.println("        children.add(" + parameters[i].getName() + ");");
			}
			mWriter.println("        return children;");
			mWriter.println("    }");

			if (!node.isAbstract()) {
				final List<Parameter> allACSLParameters = getAllACSLParameters(node);
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

	private void writeTransformerAcceptMethod(final Node node, final List<Parameter> allACSLParameters) {
		// accept method for transformer
		mWriter.println();
		mWriter.println("    public " + node.name + " accept(" + sTransformerName + " visitor) {");
		mWriter.println("        " + node.name + " node = visitor.transform(this);");
		mWriter.println("        if(node != this){");
		mWriter.println("            return node;");
		mWriter.println("        }");
		mWriter.println();

		boolean isChangedPrinted = false;

		for (final Parameter p : allACSLParameters) {
			final String newName = "new" + p.getName();
			final String listName = "tmpList" + newName;
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

			final StringBuilder sb = new StringBuilder();
			sb.append("        if(");

			if (isChangedPrinted) {
				sb.append("isChanged || ");
			}

			for (final Parameter p : allACSLParameters) {
				if (isArrayType(p)) {
					continue;
				}
				final String newName = "new" + p.getName();
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

	private boolean isArrayType(final Parameter p) {
		return p.getType().contains("[]");
	}

	private String getBaseType(final Parameter p) {
		final String typeStr = p.getType().replaceAll("\\[\\]", "");
		return typeStr;
	}

	private String getNewCallParams(final Node node) {
		if (node == null) {
			return "";
		}

		final StringBuffer sb = new StringBuffer();

		sb.append(getNewCallParams(node.getParent()));

		String comma = "";
		if (sb.length() > 0) {
			comma = ", ";
		}

		for (final Parameter p : node.getParameters()) {
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

	private void writeVisitorAcceptMethod(final Node node, final List<Parameter> allACSLParameters) {
		// accept method for visitor
		mWriter.println();
		mWriter.println("    public void accept(" + sVisitorName + " visitor) {");

		final String lineSep = System.getProperty("line.separator");

		Node parent = node.getParent();
		final String indent = "        ";
		int i = 0;
		final StringBuilder sb = new StringBuilder();
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
		for (final Parameter p : allACSLParameters) {
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

	private List<Parameter> getAllACSLParameters(final Node node) {
		final List<Parameter> allParameters = new ArrayList<>();
		Node current = node;
		while (current != null) {
			for (final Parameter p : current.getParameters()) {
				if (mGrammar.nodeTable.containsKey(getBaseType(p))) {
					allParameters.add(p);
				}
			}
			current = current.getParent();
		}
		return allParameters;
	}

	@Override
	public void setGrammar(final Grammar grammar) {
		final HashSet<String> types = new HashSet<>();
		for (final Node n : grammar.getNodeTable().values()) {
			types.add(n.name);
		}
		grammar.getNodeTable()
				.put(sVisitorName, new Node(sVisitorName, null, null, "", types, false, new Parameter[0]));
		grammar.getNodeTable().put(sTransformerName,
				new Node(sTransformerName, null, null, "", types, false, new Parameter[0]));
		super.setGrammar(grammar);
	}
}
