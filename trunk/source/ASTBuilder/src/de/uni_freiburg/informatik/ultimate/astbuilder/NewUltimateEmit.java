/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

public class NewUltimateEmit extends Emit {
	
	@Override
	public void emitClassDeclaration(Node node) throws IOException {
		mWriter.println("public " + (node.isAbstract() ? "abstract " : "") + "class " + node.getName()
				+ (node.getParent() != null ? " extends " + node.getParent().getName() : " extends BoogieASTNode")
				+ (node.getInterfaces() != null ? " implements " + node.getInterfaces() : "") + " {");
		formatComment(mWriter, "    ", "The serial version UID.");
		mWriter.println("    private static final long serialVersionUID = 1L;");
	}

	@Override
	public String getConstructorParam(Node node, boolean optional) {
		if (node == null) {
			return "loc";
		}
		return super.getConstructorParam(node, optional);
	}

	@Override
	protected void fillConstructorParamComment(Node node, StringBuffer param, StringBuffer comment, boolean optional) {
		if (node.getParent() == null) {
			param.append("ILocation loc");
			comment.append("\n@param loc the node's location");
		}
		super.fillConstructorParamComment(node, param, comment, optional);
	}

	@Override
	public void emitConstructors(Node node) throws IOException {
		int numNotWriteableParams = 1;
		int numNotOptionalParams = 1;
		int numTotalParams = 1;

		/* Default constructor is only emitted if all fields are writeable */
		/* Optional constructor is only emitted if there are optional fields */
		Node ancestor = node;
		while (ancestor != null) {
			for (final Parameter p : ancestor.parameters) {
				numTotalParams++;
				if (!p.isWriteable()) {
					numNotWriteableParams++;
				}
				if (!p.isOptional()) {
					numNotOptionalParams++;
				}
			}
			ancestor = ancestor.getParent();
		}
		if (numNotOptionalParams == 0 || numNotWriteableParams == 0) {
			formatComment(mWriter, "    ", "The default constructor.");
			mWriter.println("    public " + node.getName() + "() {");
			mWriter.println("    }");
			mWriter.println();
		}

		if (numNotOptionalParams > 0 && numNotOptionalParams < numTotalParams) {
			emitConstructor(node, false);
		}
		if (numTotalParams > 0) {
			emitConstructor(node, true);
		}
	}

	@Override
	public void emitPreamble(Node node) throws IOException {
		super.emitPreamble(node);
		mWriter.println("import java.util.List;");
		mWriter.println("import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;");
		mWriter.println("import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;");
		if (needsArraysPackage(node)) {
			mWriter.println("import java.util.Arrays;");
		}
	}

	@Override
	public void emitNodeHook(Node node) throws IOException {
		mWriter.println();
		mWriter.println("    public List<BoogieASTNode> getOutgoingNodes() {");
		mWriter.println("        List<BoogieASTNode> children = super.getOutgoingNodes();");
		final Parameter[] parameters = node.getParameters();
		System.out.println(node.getName() + " has " + parameters.length + " parameters");
		for (int i = 0; i < parameters.length; i++) {

			if (isNoRegularChild(parameters[i].getType())) {
				continue;
			}
			System.out.println(parameters[i].getName() + " is an array? " + isArray(parameters[i].getType()));

			if (isArray(parameters[i].getType())) {
				mWriter.println(String.format("        if(%s!=null){", parameters[i].getName()));
				mWriter.println(
						String.format("            children.addAll(Arrays.asList(%s));", parameters[i].getName()));
				mWriter.println("        }");
			} else {
				mWriter.println("        children.add(" + parameters[i].getName() + ");");
			}
		}
		mWriter.println("        return children;");
		mWriter.println("    }");
	}

	private boolean isNoRegularChild(String type) {
		while (type.endsWith("[]")) {
			type = type.substring(0, type.length() - 2);
		}
		return !(mGrammar.getNodeTable().containsKey(type));
	}

	private boolean needsArraysPackage(Node node) {
		for (final Parameter s : node.getParameters()) {

			if (isNoRegularChild(s.getType())) {
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
