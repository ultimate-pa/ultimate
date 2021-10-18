/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation.Race;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class DataRaceChecker {
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;
	private final ITypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeComputer;
	private final TypeSizes mTypeSizes;
	private final ProcedureManager mProcedureManager;

	private final Set<String> mRaceVars = new HashSet<>();

	public DataRaceChecker(final AuxVarInfoBuilder auxVarInfoBuilder, final MemoryHandler memoryHandler,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeComputer, final TypeSizes typeSizes,
			final ProcedureManager procMan) {
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mMemoryHandler = memoryHandler;
		mTypeHandler = typeHandler;
		mTypeSizeComputer = typeSizeComputer;
		mTypeSizes = typeSizes;
		mProcedureManager = procMan;
	}

	public void checkOnRead(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		if (mProcedureManager.isGlobalScope()) {
			// TODO find a cleaner way to fix this
			return;
		}
		if (isRaceImpossible(lrVal)) {
			return;
		}

		final Expression raceValue = createRaceRead();
		final Race[] races = updateRaceIndicator(erb, loc, lrVal, raceValue, false);
		addAssert(erb, loc, lrVal, raceValue, races);
	}

	private Expression createRaceRead() {
		return mMemoryHandler.getBooleanArrayHelper().constructFalse();
	}

	public void checkOnWrite(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		if (mProcedureManager.isGlobalScope()) {
			// TODO find a cleaner way to fix this
			return;
		}
		if (isRaceImpossible(lrVal)) {
			return;
		}

		// TODO For better performance, make the statements created by #createRaceWrite and #updateRaceIndicator atomic.
		// TODO This requires support for nested atomic blocks in CfgBuilder.LargeBlockEncoding.
		final Expression raceValue = createRaceWrite(erb, loc);
		final Race[] races = updateRaceIndicator(erb, loc, lrVal, raceValue, true);
		addAssert(erb, loc, lrVal, raceValue, races);
	}

	private Expression createRaceWrite(final ExpressionResultBuilder erb, final ILocation loc) {
		final AuxVarInfo tmp = mAuxVarInfoBuilder.constructAuxVarInfo(loc, getBoolASTType(), SFO.AUXVAR.NONDET);
		erb.addDeclaration(tmp.getVarDec());
		erb.addAuxVar(tmp);

		final Statement havoc = new HavocStatement(loc, new VariableLHS[] { tmp.getLhs() });
		erb.addStatement(havoc);

		return tmp.getExp();
	}

	private Race[] updateRaceIndicator(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal,
			final Expression newValue, final boolean isWrite) {
		final LeftHandSide[] lhs = getRaceLhs(loc, lrVal);

		final Race[] races = new Race[lhs.length];
		for (int i = 0; i < lhs.length; ++i) {
			final Statement assign = StatementFactory.constructAssignmentStatement(loc, new LeftHandSide[] { lhs[i] },
					new Expression[] { newValue });
			races[i] = DataRaceAnnotation.annotateAccess(assign, getAccessedVariable(lrVal), loc, isWrite);
			erb.addStatement(assign);
		}

		return races;
	}

	private void addAssert(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal,
			final Expression expected, final Race[] races) {
		final Check check = new Check(Spec.DATA_RACE);
		final Expression formula = ExpressionFactory.and(loc,
				Arrays.stream(getRaceExpressions(loc, erb, lrVal))
						.map(expr -> ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, expr, expected))
						.collect(Collectors.toList()));
		final Statement assertStmt = new AssertStatement(loc, formula);
		check.annotate(assertStmt);
		DataRaceAnnotation.annotateCheck(assertStmt, races, loc);
		erb.addStatement(assertStmt);
	}

	private static String getAccessedVariable(final LRValue lrVal) {
		if (lrVal instanceof LocalLValue && ((LocalLValue) lrVal).getLhs() instanceof VariableLHS) {
			return ((VariableLHS) ((LocalLValue) lrVal).getLhs()).getIdentifier();
		}
		return null;
	}

	private static boolean isRaceImpossible(final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final Expression address = ((HeapLValue) lrVal).getAddress();
			return address instanceof IdentifierExpression
					&& ((IdentifierExpression) address).getIdentifier().startsWith(SFO.FUNCTION_ADDRESS);
		}

		if (!(lrVal instanceof LocalLValue)) {
			return false;
		}
		final LocalLValue locLv = (LocalLValue) lrVal;
		if (!(locLv.getLhs() instanceof VariableLHS)) {
			return false;
		}
		final VariableLHS varLhs = (VariableLHS) locLv.getLhs();
		switch (varLhs.getDeclarationInformation().getStorageClass()) {
		case LOCAL:
		case IMPLEMENTATION_INPARAM:
		case IMPLEMENTATION_OUTPARAM:
		case PROC_FUNC:
			return true;
		default:
			return false;
		}
	}

	private LeftHandSide[] getRaceLhs(final ILocation loc, final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;
			final LeftHandSide raceLhs = mMemoryHandler.getMemoryRaceArrayLhs(loc);

			final LeftHandSide[] lhs = new LeftHandSide[getTypeSize(loc, hlv.getUnderlyingType())];
			for (int i = 0; i < lhs.length; ++i) {
				// TODO For better performance, use memory model resultion to have fewer LHS here
				final Expression ptrPlusI =
						mMemoryHandler.addIntegerConstantToPointer(loc, hlv.getAddress(), BigInteger.valueOf(i));
				lhs[i] = ExpressionFactory.constructNestedArrayLHS(loc, raceLhs, new Expression[] { ptrPlusI });
			}
			return lhs;
		}
		if (lrVal instanceof LocalLValue) {
			return new LeftHandSide[] { getRaceVariableLhs(loc, (LocalLValue) lrVal) };
		}
		throw new UnsupportedOperationException();
	}

	private Expression[] getRaceExpressions(final ILocation loc, final ExpressionResultBuilder erb,
			final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;
			final Expression raceLhs = mMemoryHandler.getMemoryRaceArray(loc);

			final Expression[] lhs = new Expression[getTypeSize(loc, hlv.getUnderlyingType())];
			for (int i = 0; i < lhs.length; ++i) {
				final Expression ptrPlusI =
						mMemoryHandler.addIntegerConstantToPointer(loc, hlv.getAddress(), BigInteger.valueOf(i));
				lhs[i] = ExpressionFactory.constructNestedArrayAccessExpression(loc, raceLhs,
						new Expression[] { ptrPlusI });
			}
			return lhs;
		}
		if (lrVal instanceof LocalLValue) {
			return new Expression[] { getRaceVariableExpression(loc, (LocalLValue) lrVal) };
		}
		throw new UnsupportedOperationException();
	}

	private int getTypeSize(final ILocation loc, final CType type) {
		final Expression operandTypeByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, type, null);
		return mTypeSizes.extractIntegerValue(operandTypeByteSizeExp, mTypeSizeComputer.getSizeT(), null)
				.intValueExact();
	}

	private Expression getRaceVariableExpression(final ILocation loc, final LocalLValue lval) {
		return ExpressionFactory.constructIdentifierExpression(loc, getBoolType(), getRaceVariableName(lval.getLhs()),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	private VariableLHS getRaceVariableLhs(final ILocation loc, final LocalLValue lval) {
		return ExpressionFactory.constructVariableLHS(loc, getBoolType(), getRaceVariableName(lval.getLhs()),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	private String getRaceVariableName(final LeftHandSide lhs) {
		final String name = "#race" + getKey(lhs);
		mRaceVars.add(name);
		return name;
	}

	private static String getKey(final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return ((VariableLHS) lhs).getIdentifier();
		}
		if (lhs instanceof StructLHS) {
			return getKey(((StructLHS) lhs).getStruct()) + "." + ((StructLHS) lhs).getField();
		}
		throw new UnsupportedOperationException("cannot create race variable for " + lhs);
	}

	public Collection<Declaration> declareRaceCheckingInfrastructure(final ILocation loc) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		decl.add(constructMemoryRaceArrayDeclaration(loc));

		final VarList vlV = new VarList(loc, mRaceVars.toArray(String[]::new), getBoolASTType());
		decl.add(new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV }));
		return decl;
	}

	private Declaration constructMemoryRaceArrayDeclaration(final ILocation loc) {
		final BoogieType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, getBoolType());
		final ASTType astType = new ArrayType(loc, boogieType, new String[0],
				new ASTType[] { mTypeHandler.constructPointerType(loc) }, getBoolASTType());
		final VarList vlV =
				new VarList(loc, new String[] { MemoryModelDeclarations.ULTIMATE_DATA_RACE_MEMORY.getName() }, astType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV });
	}

	private ASTType getBoolASTType() {
		return mMemoryHandler.getBooleanArrayHelper().constructBoolReplacementType();
	}

	private BoogieType getBoolType() {
		return mTypeHandler.getBoogieTypeForBoogieASTType(getBoolASTType());
	}
}
