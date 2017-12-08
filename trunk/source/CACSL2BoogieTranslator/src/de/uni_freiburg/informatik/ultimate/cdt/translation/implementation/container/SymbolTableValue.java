/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Container to hold the value part in the symbol table. I.e. the Boogie
 * name and the C Declaration and whether the variable is global or not.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

/**
 * @author Markus Lindenmann
 * @date 13.07.2012
 */
public class SymbolTableValue {

	/**
	 * The variable name in the Boogie program.
	 */
	private final String mBoogieName;

	/**
	 * the C-style declaration of the symbol
	 */
	private final CDeclaration mCDecl;

	/**
	 * The variable declaration in the Boogie program.
	 */
	private final Declaration mBoogieDecl;
	/**
	 * Whether the variable is a global variable in the C program or not.
	 */
	private final boolean mIsGlobalVar;

	private final boolean mIsIntFromPointer;

	private final boolean mHasConstantValue;
	private final Expression mConstantValue;

	private final IASTNode mDeclarationNode;


	/**
	 * Constructor for SymbolTableValues that don't store a constant value.
	 *
	 * @param bId
	 * @param boogieDecl
	 * @param cdecl
	 * @param isGlobal
	 * @param declNode
	 * @param isIntFromPointer
	 */
	public SymbolTableValue(final String bId, final Declaration boogieDecl, final CDeclaration cdecl,
			final boolean isGlobal, final IASTNode declNode, final boolean isIntFromPointer) {
		this(bId, boogieDecl, cdecl, isGlobal, declNode, isIntFromPointer, null);
	}


	/**
	 * Constructor.
	 *
	 * @param bId
	 *            Boogie identifier.
	 * @param cdecl
	 *            Boogie variable declaration.
	 * @param isGlobal
	 *            whether the variable is a global variable in the C program or not.
	 * @param cvar
	 *            a description of the C variable.
	 * @param isStatic
	 *            whether the variable is static in the C program or not
	 * @param isIntFromPointer
	 *            whether the variable has an int type and stores a pointer value
	 * @param constantValue
	 * 	          if the variable is known to be an alias for a constant expression (e.g. an IntegerLiteral), we give
	 *            that expression here. Example: enum entries are translated to Boogie variables, and they have a
	 *            constant integer value (which is stored in an axiom elsewhere)
	 */
	public SymbolTableValue(final String bId, final Declaration boogieDecl, final CDeclaration cdecl,
			final boolean isGlobal, final IASTNode declNode, final boolean isIntFromPointer,
			final Expression constantValue) {
		assert bId != null && !bId.equals(SFO.EMPTY);
		assert cdecl != null;
		mBoogieName = bId;
		mCDecl = cdecl;
		mBoogieDecl = boogieDecl;
		mIsGlobalVar = isGlobal;
		mDeclarationNode = declNode;
		mIsIntFromPointer = isIntFromPointer;

		if (constantValue != null) {
			mConstantValue = constantValue;
			mHasConstantValue = true;
		} else {
			mConstantValue = constantValue;
			mHasConstantValue = true;
		}
	}

	/**
	 * Return the Boogie variable name.
	 *
	 * @return the boogieName
	 */
	public String getBoogieName() {
		return mBoogieName;
	}

	/**
	 * Return the Boogie variable declaration.
	 *
	 * @return the decl
	 */
	public CDeclaration getCDecl() {
		return mCDecl;
	}

	public Declaration getBoogieDecl() {
		return mBoogieDecl;
	}

	/**
	 * Return whether the variable is global in the boogie program or not. (for instance static C variables are global
	 * boogie variables for us)
	 *
	 * @return the isGlobalVar
	 */
	public boolean isBoogieGlobalVar() {
		return mIsGlobalVar;
	}

	/**
	 * Getter for the C variable description.
	 *
	 * @return the C variable description.
	 */
	public CType getCVariable() {
		return mCDecl.getType();
	}

	public IASTNode getDeclarationNode() {
		return mDeclarationNode;
	}

	public boolean isIntFromPointer() {
		return mIsIntFromPointer;
	}

	public boolean hasConstantValue() {
		return mHasConstantValue;
	}

	public Expression getConstantValue() {
		if (!mHasConstantValue) {
			throw new IllegalStateException("check hasConstantValue() first!");
		}
		return mConstantValue;
	}


	public SymbolTableValue createMarkedIsIntFromPointer() {
		return new SymbolTableValue(mBoogieName, mBoogieDecl, mCDecl, mIsGlobalVar, mDeclarationNode, true,
				mConstantValue);
	}
}
