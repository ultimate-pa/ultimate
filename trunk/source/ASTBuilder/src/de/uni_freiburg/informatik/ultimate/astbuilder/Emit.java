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

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Emits classes etc.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
@SuppressWarnings("squid:S1192")
public class Emit {
	private static final String INDENT_SPACE = "        ";
	private static final String EMPTY_STRING = "";
	private static final String OPEN_PARENTHESIS = "(";
	private static final String CLOSE_PARENTHESIS_SEMICOLON = ");";
	private static final String COMMA = ", ";
	private static final String SEMICOLON = ";";
	private static final String STAR = " * ";
	private static final String BLANK = " ";
	private static final String BOOLEAN = "boolean";
	private static final int LENGTH_OF_TRUE_PLUS_SPACE = 5;
	private static final int MIN_NAME_LENGTH = 3;
	private static final int MAX_PARAM_LENGTH = 80;
	private static final String DEFAULT_ROOT_CONSTRUCTOR_PARAMETER = EMPTY_STRING;
	private static final List<String> BOOL_PREFIXES = Arrays.asList("is", "has");

	protected PrintWriter mWriter;
	protected Grammar mGrammar;
	protected Set<String> mEnumTypes;

	/**
	 * Constructor.
	 */
	public Emit() {
		mEnumTypes = new HashSet<>();
	}

	public void setGrammar(final Grammar grammar) {
		mGrammar = grammar;
	}

	/**
	 * @param str
	 *            String.
	 * @return capitalized string
	 */
	public static String capitalize(final String str) {
		return Character.toTitleCase(str.charAt(0)) + str.substring(1);
	}

	/**
	 * @param str
	 *            String.
	 * @return uncapitalized string
	 */
	public static String uncapitalize(final String str) {
		return Character.toLowerCase(str.charAt(0)) + str.substring(1);
	}

	/**
	 * @param str
	 *            String.
	 * @return string with spaces
	 */
	public static String breakWords(final String str) {
		final StringBuilder builder = new StringBuilder();
		final int len = str.length();
		for (int i = 0; i < len; i++) {
			final char charr = str.charAt(i);
			if (Character.isUpperCase(charr) || Character.isTitleCase(charr)) {
				if (i > 0) {
					builder.append(' ');
				}
				builder.append(Character.toLowerCase(charr));
			} else {
				builder.append(charr);
			}
		}
		return builder.toString();
	}

	/**
	 * @param className
	 *            Class name.
	 * @param name
	 *            name
	 * @param type
	 *            type
	 * @return field comment
	 */
	public static String buildFieldComment(final String className, final String name, final String type) {
		if (BOOLEAN.equals(type) && name.length() >= MIN_NAME_LENGTH && name.startsWith("is")
				&& (Character.isUpperCase(name.charAt(2)) || Character.isTitleCase(name.charAt(2)))) {
			return "True iff this " + breakWords(className) + BLANK + breakWords(name) + ".";
		}
		return "The " + breakWords(name) + " of this " + breakWords(className) + ".";
	}

	/**
	 * @param name
	 *            name.
	 * @param parent
	 *            parent
	 * @return class comment
	 */
	public static String buildClassComment(final String name, final String parent) {
		final StringBuilder builder = new StringBuilder("Represents a ");
		builder.append(breakWords(name));
		if (parent != null) {
			builder.append(" which is a special form of a ").append(Emit.breakWords(parent));
		}
		builder.append('.');
		return builder.toString();
	}

	private static String getShortComment(final String comment) {
		int end = comment.indexOf('.') + 1;
		if (end == 0) {
			end = comment.length();
		}
		return comment.substring(0, end);
	}

	protected static void formatComment(final PrintWriter writer, final String indent, final String comment) {
		writer.println(indent + "/**");
		String modifiedComment = comment;
		int nlIndex = modifiedComment.indexOf('\n');
		while (nlIndex >= 0) {
			writer.println(indent + STAR + modifiedComment.substring(0, nlIndex));
			modifiedComment = modifiedComment.substring(nlIndex + 1);
			nlIndex = modifiedComment.indexOf('\n');
		}
		writer.println(indent + STAR + modifiedComment);
		writer.println(indent + " */");
	}

	/**
	 * Emits classes.
	 *
	 * @throws IOException
	 *             if class writing fails
	 */
	public void emitClasses() throws IOException {
		for (final Node n : mGrammar.getNodeTable().values()) {
			final String name = n.getName();
			System.err.println("Building: " + name);
			mWriter = new PrintWriter(new FileWriter(name + ".java"));
			emitNode(n);
			mWriter.close();
			mWriter = null;
		}
	}

	/**
	 * @param node
	 *            node.
	 */
	public void emitPreamble(final Node node) {
		mWriter.println();
		final String pkgName = mGrammar.getPackageName();
		if (pkgName.length() > 0) {
			mWriter.println("package " + pkgName + SEMICOLON);
		}
		for (final String importStr : mGrammar.getImports()) {
			if (!importStr.endsWith(".*")) {
				boolean found = false;
				Node ancestor = node;
				while (!found && ancestor != null) {
					/* Check if type is used */
					final int dotIndex = importStr.lastIndexOf('.');
					final String type = importStr.substring(dotIndex + 1);
					if (ancestor.getUsedTypes().contains(type)) {
						found = true;
					}
					ancestor = ancestor.getParent();
				}
				if (!found) {
					continue;
				}
			}
			mWriter.println("import " + importStr + SEMICOLON);
		}
		mWriter.println();
	}

	public void emitToplevelComment(final Node node) {
		mWriter.println(String.format("/* %s -- Automatically generated by TreeBuilder */", node.getName()));
	}

	/**
	 * @param node
	 *            node.
	 */
	public void emitClassDeclaration(final Node node) {
		mWriter.println("public " + (node.isAbstract() ? "abstract " : EMPTY_STRING) + "class " + node.getName()
				+ (node.getParent() != null ? (" extends " + node.getParent().getName()) : EMPTY_STRING)
				+ (node.getInterfaces() != null ? (" implements " + node.getInterfaces()) : EMPTY_STRING) + " {");
	}

	/**
	 * @param node
	 *            node.
	 * @param optional
	 *            optional flag for adding parameter
	 * @return constructor parameter
	 */
	public String getConstructorParam(final Node node, final boolean optional) {
		if (node == null) {
			return EMPTY_STRING;
		}

		final StringBuilder builder = new StringBuilder();

		builder.append(getConstructorParam(node.getParent(), optional));

		String comma = EMPTY_STRING;
		if (builder.length() > 0) {
			comma = COMMA;
		}

		for (final Parameter parameter : node.getParameters()) {
			if (optional || !parameter.isOptional()) {
				final String pname = parameter.getName();
				builder.append(comma).append(pname);
				comma = COMMA;
			}
		}
		return builder.toString();
	}

	/**
	 * @param node
	 *            node.
	 * @return root constructor parameter
	 */
	@SuppressWarnings("static-method")
	public String getRootConstructorParam(final Node node) {
		return DEFAULT_ROOT_CONSTRUCTOR_PARAMETER;
	}

	protected void fillConstructorParamComment(final Node node, final StringBuilder constructorParams,
			final StringBuilder constructorComment, final boolean optional) {
		final Node parent = node.getParent();
		if (parent != null) {
			fillConstructorParamComment(parent, constructorParams, constructorComment, optional);
		}
		String comma = EMPTY_STRING;
		if (constructorParams.length() > 0) {
			comma = COMMA;
		}
		for (final Parameter parameter : node.getParameters()) {
			if (optional || !parameter.isOptional()) {
				final String pname = parameter.getName();
				final String pcomment = uncapitalize(getShortComment(parameter.getComment()));
				constructorComment.append("\n@param ").append(pname).append(' ').append(pcomment);
				constructorParams.append(comma);
				constructorParams.append(parameter.getType()).append(' ').append(pname);
				comma = COMMA;
			}
		}
	}

	/**
	 * @param node
	 *            node.
	 * @param optional
	 *            optional flag for adding parameter
	 */
	public void emitConstructor(final Node node, final boolean optional) {
		final String name = node.getName();
		final String parentParams;
		if (node.getParent() == null) {
			parentParams = getRootConstructorParam(node);
		} else {
			parentParams = getConstructorParam(node.getParent(), optional);
		}

		final StringBuilder constructorParams = new StringBuilder();
		final StringBuilder constructorComment = new StringBuilder("The constructor taking initial values.");
		fillConstructorParamComment(node, constructorParams, constructorComment, optional);
		formatComment(mWriter, "    ", constructorComment.toString());

		mWriter.println("    public " + name + OPEN_PARENTHESIS + constructorParams.toString() + ") {");
		if (parentParams != null) {
			mWriter.println("        super(" + parentParams + CLOSE_PARENTHESIS_SEMICOLON);
		}
		for (final Parameter parameter : node.getParameters()) {
			if (optional || !parameter.isOptional()) {
				final String pname = parameter.getName();
				mWriter.println("        this." + pname + " = " + pname + SEMICOLON);
			}
		}
		emitConstructorAfterParamAssign(node, optional);
		mWriter.println("    }");
		mWriter.println();
	}

	/**
	 * @param node
	 *            node.
	 * @param optional
	 *            optional flag
	 */
	public void emitConstructorAfterParamAssign(final Node node, final boolean optional) {
		// do nothing per default
	}

	/**
	 * @param node
	 *            node.
	 */
	public void emitConstructors(final Node node) {
		if (node == null) {
			throw new IllegalArgumentException();
		}
		int numNotWriteableParams = 0;
		int numNotOptionalParams = 0;
		int numTotalParams = 0;

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

	private void emitArrayToStringCode(final String name, final String type, final String indent, final int level) {
		final String ivar = "i" + level;
		final String modifiedType = type.substring(0, type.length() - 2);
		final String newindent = indent + INDENT_SPACE;
		String modifiedName = name;
		mWriter.println(indent + "if (" + modifiedName + " == null) {");
		mWriter.println(indent + "    sb.append(\"null\");");
		mWriter.println(indent + "} else {");
		mWriter.println(indent + "    sb.append('[');");
		mWriter.println(
				indent + "    for(int " + ivar + " = 0; " + ivar + " < " + modifiedName + ".length; " + ivar + "++) {");
		mWriter.println(newindent + "if (" + ivar + " > 0) sb.append(',');");
		modifiedName += "[" + ivar + "]";
		if (modifiedType.endsWith("[]")) {
			emitArrayToStringCode(modifiedName, modifiedType, newindent, level + 1);
		} else {
			mWriter.println(newindent + "    sb.append(" + modifiedName + CLOSE_PARENTHESIS_SEMICOLON);
		}
		mWriter.println(indent + "    }");
		mWriter.println(indent + "    sb.append(']');");
		mWriter.println(indent + "}");
	}

	/**
	 * @param node
	 *            node.
	 */
	public void emitNodeHook(final Node node) {
		// can be overridden by subclasses that want to implement a node hook
	}

	/**
	 * @param node
	 *            node.
	 */
	public void emitNode(final Node node) {
		final String name = node.getName();
		final Parameter[] parameters = node.getParameters();

		emitToplevelComment(node);
		emitPreamble(node);

		formatComment(mWriter, EMPTY_STRING, node.getComment());
		emitClassDeclaration(node);

		final boolean emitParams = parameters != null && parameters.length > 0;

		if (emitParams) {
			emitParams1(parameters);
		}

		emitConstructors(node);

		final String toStringComment = "Returns a textual description of this object.";
		formatComment(mWriter, "    ", toStringComment);
		mWriter.println("    public String toString() {");
		if (emitParams) {
			emitParams2(name, parameters);
		} else {
			mWriter.println("        return \"" + name + "\";");
		}
		mWriter.println("    }");

		if (emitParams) {
			emitParams3(parameters);
		}
		emitNodeHook(node);
		mWriter.println("}");
		mWriter.close();
	}

	private void emitParams1(final Parameter[] parameters) {
		/* collect enum types */
		for (int i = 0; i < parameters.length; i++) {
			String ptype = parameters[i].getType();
			if (ptype.startsWith("!")) {
				/* java 1.5 enum types */
				int nextComma = ptype.indexOf(',', 1);
				if (nextComma == -1) {
					nextComma = ptype.length();
				}
				final String enumName = ptype.substring(1, nextComma);
				mWriter.println("    public enum " + enumName + " {");
				StringBuilder builder = new StringBuilder();
				builder.append(INDENT_SPACE);
				String comma = EMPTY_STRING;
				ptype = ptype.substring(nextComma);
				while (ptype.length() > 0) {
					nextComma = ptype.indexOf(',', 1);
					if (nextComma == -1) {
						nextComma = ptype.length();
					}
					builder.append(comma);
					if (builder.length() + nextComma > MAX_PARAM_LENGTH) {
						mWriter.println(builder.toString());
						builder = new StringBuilder();
						builder.append(INDENT_SPACE);
					}
					builder.append(ptype.substring(1, nextComma));
					comma = COMMA;
					ptype = ptype.substring(nextComma);
				}
				mWriter.println(builder.toString());
				mWriter.println("    }");
				mWriter.println();
				parameters[i].setType(enumName);
				mEnumTypes.add(enumName);
			} else if (ptype.startsWith(",")) {
				int idx = 0;
				while (ptype.length() > 0) {
					int nextComma = ptype.indexOf(',', 1);
					if (nextComma == -1) {
						nextComma = ptype.length();
					}
					final String enumeration = ptype.substring(1, nextComma);
					mWriter.println("    public final static int " + enumeration + " = " + idx + SEMICOLON);
					idx++;
					ptype = ptype.substring(nextComma);
				}
				mWriter.println();
				parameters[i].setType("int");
			}
		}

		for (int i = 0; i < parameters.length; i++) {
			formatComment(mWriter, "    ", parameters[i].getComment());
			mWriter.println("    " + parameters[i].getType() + BLANK + parameters[i].getName() + SEMICOLON);
			mWriter.println();
		}
	}

	private void emitParams2(final String name, final Parameter[] parameters) {
		mWriter.println("        StringBuffer sb = new StringBuffer();");
		mWriter.println("        sb.append(\"" + name + "\").append('[');");
		String comma = EMPTY_STRING;
		for (int i = 0; i < parameters.length; i++) {
			final String pname = parameters[i].getName();
			final String ptype = parameters[i].getType();
			if (ptype.endsWith("[]")) {
				if (!EMPTY_STRING.equals(comma)) {
					mWriter.println("        sb" + comma + SEMICOLON);
				}
				emitArrayToStringCode(pname, ptype, INDENT_SPACE, 1);
			} else {
				mWriter.println("        sb" + comma + ".append(" + pname + CLOSE_PARENTHESIS_SEMICOLON);
			}
			comma = ".append(',')";
		}
		mWriter.println("        return sb.append(']').toString();");
	}

	private void emitParams3(final Parameter[] parameters) {
		for (int i = 0; i < parameters.length; i++) {
			mWriter.println();

			final String pname = parameters[i].getName();
			final String ptype = parameters[i].getType();
			final String pcomment = parameters[i].getComment();
			final String cpname = capitalize(pname);
			String getName = "get" + cpname;
			String setName = "set" + cpname;
			String getComment;
			String setComment;
			if (BOOLEAN.equals(ptype)) {
				int index = 0;
				for (final String prefix : BOOL_PREFIXES) {
					if (pname.startsWith(prefix)) {
						index = prefix.length();
						break;
					}
				}
				if (index > 0) {
					getName = pname;
					setName = "set" + pname.substring(index);
				}
				String nonTrueComment = pcomment;
				if (nonTrueComment.startsWith("True ")) {
					nonTrueComment = nonTrueComment.substring(LENGTH_OF_TRUE_PLUS_SPACE);
				}
				getComment = "Checks " + uncapitalize(nonTrueComment) + "\n@return "
						+ uncapitalize(getShortComment(pcomment));
				setComment = "Sets " + uncapitalize(nonTrueComment) + "\n@param " + pname + BLANK
						+ uncapitalize(getShortComment(pcomment));
			} else {
				getComment = "Gets " + uncapitalize(pcomment) + "\n@return " + uncapitalize(getShortComment(pcomment));
				setComment = "Sets " + uncapitalize(pcomment) + "\n@param " + pname + BLANK
						+ uncapitalize(getShortComment(pcomment));
			}
			formatComment(mWriter, "    ", getComment);
			mWriter.println("    public " + ptype + BLANK + getName + "() {");
			mWriter.println("        return " + pname + SEMICOLON);
			mWriter.println("    }");

			if (parameters[i].isWriteable()) {
				mWriter.println();
				formatComment(mWriter, "    ", setComment);
				mWriter.println("    public void " + setName + OPEN_PARENTHESIS + ptype + BLANK + pname + ") {");
				if (parameters[i].isWriteableOnce) {
					mWriter.println("        //Writeable only once");
					mWriter.println("        if(this." + pname + " != null && " + pname + " != this." + pname + "){");
					mWriter.println("                throw new AssertionError(\"Value is only writeable once\");");
					mWriter.println("        }");
				}
				mWriter.println("        this." + pname + " = " + pname + SEMICOLON);
				mWriter.println("    }");
			}
		}
	}
}
