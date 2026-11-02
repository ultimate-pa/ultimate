/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirToBoogie plug-in.
 * It is used to monitor the parsing of LLVM IR files and to translate them into a Boogie AST.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations;

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.util.ArrayList;
import java.util.Optional;

import org.antlr.v4.runtime.ParserRuleContext;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

/**
 * Builders for Boogie variable declarations, specifications and struct types used by the translation of LLVM-IR to
 * Boogie.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class DeclarationBuilder {

	private DeclarationBuilder() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs a variable declaration from a type and identifier.
	 *
	 * This method constructs a VariableDeclaration object with the specified type and identifier, using the provided
	 * location for the declaration.
	 *
	 * @param type
	 *            The type of the variable (e.g., "int", "bool").
	 * @param identifier
	 *            The identifier for the variable.
	 * @param location
	 *            The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 */
	public static VariableDeclaration constructVarDecFromString(final String type, final String identifier,
			final LlvmirLocation location) {
		final PrimitiveType primType = new PrimitiveType(location, type);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, primType);
		return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
	}

	/**
	 * Constructs a variable declaration from a type context, identifier, and location.
	 *
	 * This method constructs a VariableDeclaration object based on the provided type context and identifier.
	 *
	 * @param typeContext
	 *            The type context from which to extract the type information.
	 * @param identifier
	 *            The identifier for the variable.
	 * @param location
	 *            The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 * @throws AssertionError
	 *             if the type context is not supported or does not contain an intType.
	 */
	public static VariableDeclaration constructVarDecFromTypeContext(final ParserRuleContext typeContext,
			final String identifier, final LlvmirLocation location) throws AssertionError {
		final LLVMIRParser.IntTypeContext intType;

		if (typeContext instanceof LLVMIRParser.ConcreteTypeContext) {
			intType = ((LLVMIRParser.ConcreteTypeContext) typeContext).intType();
		} else if (typeContext instanceof LLVMIRParser.TypeContext) {
			intType = ((LLVMIRParser.TypeContext) typeContext).intType();
		} else {
			throw new AssertionError("Unsupported type context for variable declaration:");
		}

		if (intType == null) {
			throw new AssertionError("Type context does not contain an intType:");
		}

		final String typeString = intType.getText();
		final String typeIdentifier = typeString.equals("i1") ? "bool" : "int";

		final PrimitiveType type = new PrimitiveType(location, typeIdentifier);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, type);
		return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
	}

	/**
	 * Constructs a specification from a given identifier and location.
	 *
	 * This method constructs a ModifiesSpecification that indicates the specified variable is modified in the Boogie
	 * AST.
	 *
	 * @param identifier
	 *            The identifier of the variable to be modified.
	 * @param location
	 *            The location in the source code where this specification is defined.
	 * @return A ModifiesSpecification object representing the modifies specification for the given identifier.
	 */
	public static ModifiesSpecification constructSpecFromIdentifier(final String identifier,
			final LlvmirLocation location) {
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		return new ModifiesSpecification(location, false, new VariableLHS[] { varLhs });
	}

	/**
	 * This method searches the list of declarations for a TypeDeclaration with an identifier matching the format
	 * "i{bitLength}Pair".
	 *
	 * @param bitLength
	 *            The bit length to check for.
	 * @param declarations
	 *            The list of declarations to search.
	 * @return true if a matching TypeDeclaration exists, false otherwise.
	 */
	public static boolean bitLengthPairExists(final int bitLength, final ArrayList<Declaration> declarations) {
		final Optional<TypeDeclaration> typeDec =
				declarations.stream().filter(dec -> dec instanceof TypeDeclaration).map(dec -> (TypeDeclaration) dec)
						.filter(typeDecl -> typeDecl.getIdentifier().equals("i" + bitLength + "Pair")).findFirst();
		return typeDec.isPresent();
	}

	/**
	 * Constructs the declaration of the struct type that holds the result of an LLVM operation with overflow.
	 *
	 * The struct type "i{bitLength}Pair" has the field e0 of type int for the result and the field e1 of type bool for
	 * the overflow flag.
	 *
	 * @param bitLength
	 *            The bit length of the integer type of the operation.
	 * @param location
	 *            The location in the source code where this type is needed.
	 * @return A TypeDeclaration representing the struct type for the given bit length.
	 */
	public static TypeDeclaration constructBitLengthPairTypeDeclaration(final int bitLength,
			final LlvmirLocation location) {
		final ArrayList<VarList> varLists = new ArrayList<>();
		final PrimitiveType intType = new PrimitiveType(location, "int");
		final VarList varList1 = new VarList(location, new String[] { "e0" }, intType);
		varLists.add(varList1);
		final PrimitiveType boolType = new PrimitiveType(location, "bool");
		final VarList varList2 = new VarList(location, new String[] { "e1" }, boolType);
		varLists.add(varList2);
		final StructType structType = new StructType(location, varLists.toArray(VarList[]::new));
		return new TypeDeclaration(location, new Attribute[] {}, true, "i" + bitLength + "Pair", new String[] {},
				structType);
	}
}