/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
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

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

/**
 * Result that is returned whenever we dispatch a type specifier.
 *
 * TODO 2018-10-22 Matthias: It seems that this kind of result is
 * (sometimes) also returned when we dispatch a type declaration.
 * I think this is not desired any more and happens only for
 * historical reasons.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 09.02.2012
 */
public class TypesResult extends Result {

	/**
	 * We need this flag to determine, if this declaration is a constant or not.
	 */
	private final boolean mIsConst;
	/**
	 * Whether the type is void, which is not directly representable in Boogie.
	 */
	private final boolean mIsVoid;
	/**
	 * C variable description.
	 */
	private final CType mCType;

	/**
	 * Constructor.
	 *
	 * @param node
	 *            the BoogieASTNode to hold.
	 * @param isConst
	 *            boolean flag to determine constant.
	 * @param isVoid
	 *            boolean flag to determine void.
	 * @param cvar
	 *            a description of the C variable.
	 */
	public TypesResult(final ASTType node, final boolean isConst, final boolean isVoid, final CType cvar) {
		super(node);
		mIsConst = isConst;
		mIsVoid = isVoid;
		mCType = cvar;
	}

	public ASTType getAstType() {
		return (ASTType) super.getNode();
	}

	public boolean isConst() {
		return mIsConst;
	}

	public boolean isVoid() {
		return mIsVoid;
	}

	public CType getCType() {
		return mCType;
	}

	@Override
	public String toString() {
		return "ResultTypes: " + mCType;
	}

	public static TypesResult create(final TypesResult resType, final CType cType) {
		return new TypesResult(resType.getAstType(), resType.isConst(), resType.isVoid(), cType);
	}

}
