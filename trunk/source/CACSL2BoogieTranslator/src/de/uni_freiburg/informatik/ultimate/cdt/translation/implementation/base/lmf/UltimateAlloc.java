/*
 * Copyright (C) 2013-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.lmf;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateAlloc extends BaseCModelFeatureDefinition {

	/**
	 * The "~size" variable identifier.
	 */
	private static final String SIZE = "~size";

	@Override
	public String getName() {
		return SFO.ALLOC;
	}

	@Override
	public CModelFeature getFeature() {
		return CModelFeature.ULTIMATE_ALLOC;
	}

	@Override
	public EnumSet<CModelFeature> getRequirements() {
		return null;
	}

	/**
	 * Generate <code>procedure ~Ultimate.alloc(~size:int) returns (#res:$Pointer$);</code>'s declaration and
	 * implementation.
	 *
	 * @param typeHandler
	 *
	 * @param tuLoc
	 *            the location for the new nodes.
	 * @param mExpressionTranslation
	 * @param mTypeSizes
	 * @param mProcedureManager
	 * @return declaration and implementation of procedure <code>~malloc</code>
	 */
	public ArrayList<Declaration> declareMalloc(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc, final IASTNode hook, final MemoryArea memArea,
			final ExpressionTranslation mExpressionTranslation, final TypeSizes mTypeSizes,
			final ProcedureManager mProcedureManager) {
		final ASTType intType = typeHandler.cType2AstType(tuLoc, mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression nr0 = mTypeSizes.constructLiteralForIntegerType(tuLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final Expression valid = getValidArray(tuLoc);
		// procedure ~malloc(~size:int) returns (#res:$Pointer$);
		// requires ~size >= 0;
		// ensures old(#valid)[#res!base] = false;
		// ensures #valid = old(#valid)[#res!base := true];
		// ensures #res!offset == 0;
		// ensures #res!base != 0;
		// ensures #length = old(#length)[#res!base := ~size];
		// modifies #length, #valid;
		final Expression res = // new IdentifierExpression(tuLoc, SFO.RES);
				ExpressionFactory.constructIdentifierExpression(tuLoc, typeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, getName()));

		final Expression length = getLengthArray(tuLoc);
		// #res!base
		final Expression resBase = ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE);
		// { #res!base }
		final Expression[] idcMalloc = new Expression[] { resBase };
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();

		// ~size
		final IdentifierExpression size = // new IdentifierExpression(tuLoc, SIZE);
				ExpressionFactory.constructIdentifierExpression(tuLoc, BoogieType.TYPE_INT, SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, getName()));

		{
			final Procedure allocDeclaration = new Procedure(tuLoc, new Attribute[0], getName(), new String[0],
					new VarList[] { new VarList(tuLoc, new String[] { SIZE }, intType) },
					new VarList[] {
							new VarList(tuLoc, new String[] { SFO.RES }, typeHandler.constructPointerType(tuLoc)) },
					new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, tuLoc, getName(), allocDeclaration);
		}

		final List<Specification> specMalloc = new ArrayList<>();

		// old(#valid)[#res!base] == false
		specMalloc
				.add(mProcedureManager
						.constructEnsuresSpecification(tuLoc, false,
								ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
										ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
												ExpressionFactory.constructUnaryExpression(tuLoc,
														UnaryExpression.Operator.OLD, valid),
												idcMalloc),
										bLFalse),
								Collections.emptySet()));
		// #valid == old(#valid)[#res!base := true]
		specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ensuresArrayUpdate(tuLoc, bLTrue, resBase, valid),
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(valid))));
		// #res!offset == 0
		specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
						ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_OFFSET), nr0),
				Collections.emptySet()));
		// #res!base != 0
		specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ,
						ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE), nr0),
				Collections.emptySet()));
		if (memArea == MemoryArea.HEAP) {
			// #StackHeapBarrier < res!base
			specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
							IASTBinaryExpression.op_lessThan, getStackHeapBarrier(tuLoc),
							mExpressionTranslation.getCTypeOfPointerComponents(),
							ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE),
							mExpressionTranslation.getCTypeOfPointerComponents()),
					Collections.emptySet()));
		}
		if (memArea == MemoryArea.STACK) {
			// #StackHeapBarrier < res!base
			specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
							IASTBinaryExpression.op_lessThan,
							ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE),
							mExpressionTranslation.getCTypeOfPointerComponents(),
							ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE),
							mExpressionTranslation.getCTypeOfPointerComponents()),
					Collections.emptySet()));
		}

		// #length == old(#length)[#res!base := ~size]
		specMalloc
				.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
						ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, length,
								ExpressionFactory.constructArrayStoreExpression(tuLoc,
										ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD,
												length),
										idcMalloc, size)),
						Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(length))));
		mProcedureManager.addSpecificationsToCurrentProcedure(specMalloc);

		final ArrayList<Declaration> result = new ArrayList<>();
		if (ADD_IMPLEMENTATIONS) {
			final Expression addr = ExpressionFactory.constructIdentifierExpression(tuLoc,
					mTypeHandler.getBoogiePointerType(), ADDR,
					new DeclarationInformation(StorageClass.LOCAL, MemoryModelDeclarations.ULTIMATE_ALLOC.getName()));
			final Expression addrOffset =
					ExpressionFactory.constructStructAccessExpression(tuLoc, addr, SFO.POINTER_OFFSET);
			final Expression addrBase =
					ExpressionFactory.constructStructAccessExpression(tuLoc, addr, SFO.POINTER_BASE);
			// procedure ~malloc(~size:int) returns (#res:pointer) {
			// var ~addr : pointer;
			//
			// assume ~addr!offset = 0;
			// assume ~addr!base != 0;
			// assume !#valid[~addr!base];
			// // #valid setzen
			// #valid = #valid[~addr!base := true];
			// #length = #length[~addr!base := size];
			// // return pointer
			// #res := ~addr;
			// }
			final Expression[] idcAddrBase = new Expression[] { addrBase };
			final VariableDeclaration[] localVars =
					new VariableDeclaration[] { new VariableDeclaration(tuLoc, new Attribute[0], new VarList[] {
							new VarList(tuLoc, new String[] { ADDR }, typeHandler.constructPointerType(tuLoc)) }) };

			final VariableLHS resLhs = ExpressionFactory.constructVariableLHS(tuLoc, typeHandler.getBoogiePointerType(),
					SFO.RES, new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, getName()));
			final Statement[] block = new Statement[6];
			block[0] = new AssumeStatement(tuLoc,
					ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, addrOffset, nr0));
			block[1] = new AssumeStatement(tuLoc,
					ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ, addrBase, nr0));
			block[2] = new AssumeStatement(tuLoc,
					ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.LOGICNEG,
							ExpressionFactory.constructNestedArrayAccessExpression(tuLoc, valid, idcAddrBase)));
			block[3] =
					StatementFactory.constructAssignmentStatement(tuLoc, new LeftHandSide[] { getValidArrayLhs(tuLoc) },
							new Expression[] { new ArrayStoreExpression(tuLoc, valid, idcAddrBase, bLTrue) });
			block[4] = StatementFactory.constructAssignmentStatement(tuLoc,
					new LeftHandSide[] { getLengthArrayLhs(tuLoc) },
					new Expression[] { new ArrayStoreExpression(tuLoc, length, idcAddrBase, size) });
			block[5] = StatementFactory.constructAssignmentStatement(tuLoc, new LeftHandSide[] { resLhs },
					new Expression[] { addr });

			final Body bodyMalloc = mProcedureManager.constructBody(tuLoc, localVars, block, getName());
			result.add(new Procedure(tuLoc, new Attribute[0], getName(), new String[0],
					new VarList[] { new VarList(tuLoc, new String[] { SIZE }, intType) },
					new VarList[] {
							new VarList(tuLoc, new String[] { SFO.RES }, typeHandler.constructPointerType(tuLoc)) },
					null, bodyMalloc));
		}
		mProcedureManager.endCustomProcedure(main, getName());
		return result;
	}

}
