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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * We often need to deal with auxiliary variables during translation. Several objects may be related to an auxvar: A
 * declaration, a LeftHandSide, an Expression, ... This class stores all of these for one auxvar.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AuxVarInfoBuilder {

	private final INameHandler mNameHandler;
	private final ITypeHandler mTypeHandler;
	private final ProcedureManager mProcedureManager;

	public AuxVarInfoBuilder(final INameHandler nameHandler, final ITypeHandler typeHandler,
			final ProcedureManager procedureManager) {
		mNameHandler = nameHandler;
		mTypeHandler = typeHandler;
		mProcedureManager = procedureManager;
	}

	public AuxVarInfo constructAuxVarInfo(final ILocation loc, final CType cType) {
		final AUXVAR auxVarType;
		if (cType instanceof CArray) {
			auxVarType = SFO.AUXVAR.ARRAYINIT;
		} else if (cType instanceof CStructOrUnion) {
			auxVarType = SFO.AUXVAR.STRUCTINIT;
		} else {
			throw new UnsupportedOperationException();
		}
		return constructAuxVarInfo(loc, cType, auxVarType);
	}

	public AuxVarInfo constructAuxVarInfo(final ILocation loc, final CType cType, final AUXVAR auxVarType) {
		final String id = mNameHandler.getTempVarUID(auxVarType, cType);
		final ASTType astType = mTypeHandler.cType2AstType(loc, cType);

		return constructAuxVarHelper(loc, id, astType, mProcedureManager.isGlobalScope());
	}

	public AuxVarInfo constructAuxVarInfo(final ILocation loc, final CType cType, final ASTType astType,
			final AUXVAR auxVarType) {
		final String id = mNameHandler.getTempVarUID(auxVarType, cType);
		return constructAuxVarHelper(loc, id, astType, false);
	}

	public AuxVarInfo constructAuxVarInfo(final ILocation loc, final ASTType astType, final AUXVAR auxVarType) {
		final String id = mNameHandler.getTempVarUID(auxVarType, null);
		return constructAuxVarHelper(loc, id, astType, false);
	}

	public AuxVarInfo constructGlobalAuxVarInfo(final ILocation loc, final CType cType, final AUXVAR auxVarType) {
		final String id = mNameHandler.getTempVarUID(auxVarType, cType);
		final ASTType astType = mTypeHandler.cType2AstType(loc, cType);

		return constructAuxVarHelper(loc, id, astType, true);
	}

	private AuxVarInfo constructAuxVarHelper(final ILocation loc, final String id, final ASTType astType,
			final boolean isGlobal) {

		final DeclarationInformation declInfo = isGlobal ? DeclarationInformation.DECLARATIONINFO_GLOBAL
				: new DeclarationInformation(StorageClass.LOCAL, mProcedureManager.getCurrentProcedureID());
		return constructAuxVarHelper(loc, id, astType, declInfo);
	}

	private AuxVarInfo constructAuxVarHelper(final ILocation loc, final String id, final ASTType astType,
			final DeclarationInformation declInfo) {
		final VariableDeclaration decl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { id }, astType) });


		final VariableLHS lhs = ExpressionFactory.constructVariableLHS(loc,
				mTypeHandler.getBoogieTypeForBoogieASTType(astType), id, declInfo);

		final IdentifierExpression exp = ExpressionFactory.constructIdentifierExpression(loc,
				mTypeHandler.getBoogieTypeForBoogieASTType(astType), id, declInfo);

		return new AuxVarInfo(decl, lhs, exp);
	}

	/**
	 * Normal aux vars are havocced as soon as possible (once we arrive at "statement level" in the translated C
	 * program).
	 * Some aux vars are havocced only when the scope (procedure) is left
	 *
	 * @param loc
	 * @param cType
	 * @param declInfo
	 * @param compoundliteral
	 * @return
	 */
	public AuxVarInfo constructAuxVarInfoForBlockScope(final ILocation loc, final CType cType,
			final AUXVAR auxVarType, final DeclarationInformation declInfo) {
		assert auxVarType == SFO.AUXVAR.COMPOUNDLITERAL : "only block-scope aux vars are allowed here (extend the "
				+ "assertion if you added a new one)";

		final String id = mNameHandler.getTempVarUIDForBlockScope(auxVarType, cType);
		final ASTType astType = mTypeHandler.cType2AstType(loc, cType);

		return constructAuxVarHelper(loc, id, astType, declInfo);

	}

}
