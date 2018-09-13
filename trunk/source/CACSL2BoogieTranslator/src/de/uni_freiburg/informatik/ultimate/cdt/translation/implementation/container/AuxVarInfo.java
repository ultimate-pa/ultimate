/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.BoogieTypeHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * We often need to deal with auxiliary variables during translation.
 * Several objects may be related to an auxvar: A declaration, a LeftHandSide, an Expression, ...
 * This class stores all of these for one auxvar.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class AuxVarInfo {

	private final VariableDeclaration mVarDec;
	private final VariableLHS mLhs;
	private final IdentifierExpression mExp;

	public AuxVarInfo(final VariableDeclaration varDec, final VariableLHS lhs, final IdentifierExpression exp) {
		assert varDec.getVariables().length == 1 : "we allow precisely one identifier per aux var at the moment";
		assert varDec.getVariables()[0].getIdentifiers().length == 1 : "we allow precisely one identifier per aux var "
				+ "at the moment";
		mVarDec = varDec;
		mLhs = lhs;
		mExp = exp;
	}

	public VariableDeclaration getVarDec() {
		return mVarDec;
	}

	public VariableLHS getLhs() {
		return mLhs;
	}

	public IdentifierExpression getExp() {
		return mExp;
	}

	@Override
	public String toString() {
		return "AuxVarInfo [mVarDec=" + mVarDec + ", mLhs=" + mLhs + ", mExp=" + mExp + "]";
	}

	public static AuxVarInfo constructAuxVarInfo(final ILocation loc, final Dispatcher main, final CType cType) {
		final AUXVAR auxVarType;
		if (cType instanceof CArray) {
			auxVarType = SFO.AUXVAR.ARRAYINIT;
		} else if (cType instanceof CStruct) {
			auxVarType = SFO.AUXVAR.STRUCTINIT;
		} else {
			throw new UnsupportedOperationException();
		}
		return constructAuxVarInfo(loc, main, cType, auxVarType);
	}

	public static AuxVarInfo constructAuxVarInfo(final ILocation loc, final Dispatcher main, final CType cType,
					final AUXVAR auxVarType) {
		final String id = main.mNameHandler.getTempVarUID(auxVarType, cType);
		final ASTType astType = main.mTypeHandler.cType2AstType(loc, cType);

		return constructAuxVarHelper(loc, main, id, astType, false);
	}

	public static AuxVarInfo constructAuxVarInfo(final ILocation loc, final Dispatcher main, final CType cType,
				final ASTType astType, final AUXVAR auxVarType) {

			final String id = main.mNameHandler.getTempVarUID(auxVarType, cType);
	//		final ASTType astType = main.mTypeHandler.cType2AstType(loc, cType);
			return constructAuxVarHelper(loc, main, id, astType, false);
		}

	public static AuxVarInfo constructAuxVarInfo(final ILocation loc, final Dispatcher main, final ASTType astType,
					final AUXVAR auxVarType) {
		final String id = main.mNameHandler.getTempVarUID(auxVarType, null);

		return constructAuxVarHelper(loc, main, id, astType, false);
	}

	public static AuxVarInfo constructGlobalAuxVarInfo(final ILocation loc, final Dispatcher main,
			final CType cType, final AUXVAR auxVarType) {
		final String id = main.mNameHandler.getTempVarUID(auxVarType, cType);
		final ASTType astType = main.mTypeHandler.cType2AstType(loc, cType);

		return constructAuxVarHelper(loc, main, id, astType, true);
	}

	private static AuxVarInfo constructAuxVarHelper(final ILocation loc, final Dispatcher main, final String id,
			final ASTType astType, final boolean isGlobal) {
		final VariableDeclaration decl = new VariableDeclaration(loc,
				new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { id }, astType ) });

		final BoogieTypeHelper boogieTypeHelper = main.mCHandler.getBoogieTypeHelper();

		final DeclarationInformation declInfo = isGlobal ?
					DeclarationInformation.DECLARATIONINFO_GLOBAL :
				new DeclarationInformation(StorageClass.LOCAL,
						main.mCHandler.getProcedureManager().getCurrentProcedureID());


		final VariableLHS lhs = ExpressionFactory.constructVariableLHS(loc,
						boogieTypeHelper.getBoogieTypeForBoogieASTType(astType), id, declInfo);

		final IdentifierExpression exp = ExpressionFactory.constructIdentifierExpression(loc,
						boogieTypeHelper.getBoogieTypeForBoogieASTType(astType), id, declInfo);

		return new AuxVarInfo(decl, lhs, exp);
	}


}
