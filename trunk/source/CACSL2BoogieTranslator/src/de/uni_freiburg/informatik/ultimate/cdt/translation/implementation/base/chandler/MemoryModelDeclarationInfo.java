/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Holds information about a memory model declaration, including its associated declaration type and optional Boogie
 * type.
 *
 * @author Jan Körner
 */
public class MemoryModelDeclarationInfo {
	private final MemoryModelDeclarations mMmd;
	private final BoogieType mBoogieType;

	/**
	 * Constructs a {@code MemoryModelDeclarationInfo} with the specified declaration type.
	 *
	 * The Boogie type is set to null.
	 *
	 * @param mmd
	 *            The memory model declaration type.
	 */
	public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		mMmd = mmd;
		mBoogieType = null;
	}

	/**
	 * Constructs a {@code MemoryModelDeclarationInfo} with the specified declaration type and associated Boogie type.
	 *
	 * @param mmd
	 *            The memory model declaration type.
	 * @param boogieType
	 *            The Boogie type associated with this declaration.
	 */
	public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd, final BoogieType boogieType) {
		mMmd = mmd;
		mBoogieType = boogieType;
	}

	/**
	 * Constructs an identifier expression for this memory model declaration at a given location.
	 *
	 * @param loc
	 *            The source location for the expression.
	 * @return An {@link IdentifierExpression} representing this declaration.
	 */
	IdentifierExpression constructIdentifierExpression(final ILocation loc) {
		return ExpressionFactory.constructIdentifierExpression(loc, mBoogieType, mMmd.getName(),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	/**
	 * Constructs a variable left-hand side (LHS) for this memory model declaration at a given location.
	 *
	 * @param loc
	 *            The source location for the variable.
	 * @return A {@link VariableLHS} representing this declaration.
	 */
	VariableLHS constructVariableLHS(final ILocation loc) {
		return ExpressionFactory.constructVariableLHS(loc, mBoogieType, mMmd.getName(),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	/**
	 * Retrieves the Boogie type associated with this declaration.
	 *
	 * @return The {@link BoogieType} associated with this declaration.
	 * @throws IllegalStateException
	 *             if the Boogie type is null.
	 */
	BoogieType getBoogieType() {
		if (mBoogieType == null) {
			throw new IllegalStateException();
		}
		return mBoogieType;
	}
}
