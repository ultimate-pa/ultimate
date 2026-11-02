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

import java.util.ArrayList;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

/**
 * Builders for the Boogie type declarations used by the translation of LLVM-IR to Boogie: the struct types that hold
 * the results of LLVM operations with overflow.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class TypeDeclarationBuilder {

	private TypeDeclarationBuilder() {
		// utility class, not meant to be instantiated
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