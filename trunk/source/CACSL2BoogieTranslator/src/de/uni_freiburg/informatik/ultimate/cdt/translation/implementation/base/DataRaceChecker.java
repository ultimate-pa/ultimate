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
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
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
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CAtomic;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation.Race;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

public final class DataRaceChecker {
	private static final boolean SUPPORT_ARRAY_STRUCT_LHS = true;

	private static final String UNSUPPORTED_MSG =
			"Race detection currently only supports simple variables and data on heap. "
					+ "Structs and arrays are not yet supported (unless they are on the heap).";

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;
	private final ITypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeComputer;
	private final TypeSizes mTypeSizes;
	private final ProcedureManager mProcedureManager;
	private final FunctionDeclarations mFunDecl;
	private final boolean mIsPreRun;

	private final Map<String, BoogieType> mRaceIndicators = new HashMap<>();

	public DataRaceChecker(final AuxVarInfoBuilder auxVarInfoBuilder, final MemoryHandler memoryHandler,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeComputer, final TypeSizes typeSizes,
			final ProcedureManager procMan, final FunctionDeclarations funDecl, final boolean isPreRun) {
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mMemoryHandler = memoryHandler;
		mTypeHandler = typeHandler;
		mTypeSizeComputer = typeSizeComputer;
		mTypeSizes = typeSizes;
		mProcedureManager = procMan;
		mFunDecl = funDecl;
		mIsPreRun = isPreRun;
	}

	/**
	 * Adds a data race check appropriate for read accesses.
	 *
	 * @param erb
	 *            An {@link ExpressionResultBuilder} to which the data race check statements are added
	 * @param loc
	 * @param lrVal
	 *            The value being read
	 */
	public void checkOnRead(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		if (mProcedureManager.isGlobalScope()) {
			// TODO find a cleaner way to fix this
			return;
		}
		if (isRaceImpossible(lrVal)) {
			return;
		}

		if (!SUPPORT_ARRAY_STRUCT_LHS && isUnsupportedArrayOrStruct(lrVal)) {
			if (mIsPreRun) {
				// call #getMemoryRaceArray to make sure it is marked as required
				mMemoryHandler.getMemoryRaceArray(loc);
				return;
			}
			// should be moved to heap in main run
			throw new UnsupportedOperationException(UNSUPPORTED_MSG);
		}

		final Expression raceValue = createRaceRead();
		final Race[] races = updateRaceIndicator(erb, loc, lrVal, raceValue, false);
		addAssert(erb, loc, lrVal, raceValue, races);
	}

	private static boolean isUnsupportedArrayOrStruct(final LRValue lrVal) {
		if (lrVal instanceof LocalLValue) {
			final LocalLValue locVal = (LocalLValue) lrVal;
			return !(locVal.getLhs() instanceof VariableLHS);
		}
		return false;
	}

	private Expression createRaceRead() {
		return mMemoryHandler.getBooleanArrayHelper().constructFalse();
	}

	/**
	 * Adds a data race check appropriate for write accesses.
	 *
	 * @param erb
	 *            An {@link ExpressionResultBuilder} to which the data race check statements and declarations are added
	 * @param loc
	 * @param lrVal
	 *            The value being written
	 */
	public void checkOnWrite(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		if (mProcedureManager.isGlobalScope()) {
			// TODO find a cleaner way to fix this
			return;
		}
		if (isRaceImpossible(lrVal)) {
			return;
		}

		if (!SUPPORT_ARRAY_STRUCT_LHS && isUnsupportedArrayOrStruct(lrVal)) {
			if (mIsPreRun) {
				// call #getMemoryRaceArray to make sure it is marked as required
				mMemoryHandler.getMemoryRaceArray(loc);
				return;
			}
			// should be moved to heap in main run
			throw new UnsupportedOperationException(UNSUPPORTED_MSG);
		}

		// TODO For better performance, make the statements created by #createRaceWrite and #updateRaceIndicator atomic.
		// TODO This requires support for nested atomic blocks in CfgBuilder.LargeBlockEncoding.
		final Expression raceValue = createRaceWrite(erb, loc);
		final Race[] races = updateRaceIndicator(erb, loc, lrVal, raceValue, true);
		addAssert(erb, loc, lrVal, raceValue, races);
	}

	private Expression createRaceWrite(final ExpressionResultBuilder erb, final ILocation loc) {
		final AuxVarInfo tmp = mAuxVarInfoBuilder.constructAuxVarInfo(loc, getBoolASTType(), SFO.AUXVAR.NONDET);
		erb.addAuxVarWithDeclaration(tmp);

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
					new Expression[] { wrapRaceIndicatorValue(loc, newValue, lhs[i].getType()) });
			races[i] = DataRaceAnnotation.annotateAccess(assign, getAccessPath(lrVal), loc, isWrite);
			erb.addStatement(assign);
		}

		return races;
	}

	private void addAssert(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal,
			final Expression expected, final Race[] races) {
		final Check check = new Check(Spec.DATA_RACE);
		final Expression formula =
				ExpressionFactory.and(loc,
						getRaceExpressions(loc, lrVal)
								.map(expr -> ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, expr,
										wrapRaceIndicatorValue(loc, expected, expr.getType())))
								.collect(Collectors.toList()));
		final Statement assertStmt = new AssertStatement(loc, formula);
		check.annotate(assertStmt);
		DataRaceAnnotation.annotateCheck(assertStmt, races, loc);
		erb.addStatement(assertStmt);
	}

	private static String getAccessPath(final LRValue lrVal) {
		if (lrVal instanceof LocalLValue) {
			final ImmutableList<String> path = getAccessPath(((LocalLValue) lrVal).getLhs());
			if (path == null) {
				return null;
			}
			return path.stream().collect(Collectors.joining("->"));
		}
		return null;
	}

	private static ImmutableList<String> getAccessPath(final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return ImmutableList.singleton(((VariableLHS) lhs).getIdentifier());
		}
		if (lhs instanceof StructLHS) {
			final ImmutableList<String> prefix = getAccessPath(((StructLHS) lhs).getStruct());
			if (prefix == null) {
				return null;
			}
			return new ImmutableList<>(((StructLHS) lhs).getField(), prefix);
		}
		if (lhs instanceof ArrayLHS) {
			return null;
		}
		throw new IllegalArgumentException("unknown type of LHS: " + lhs);
	}

	private static boolean isRaceImpossible(final LRValue lrVal) {
		if (lrVal.getCType() instanceof CAtomic) {
			// Atomic types cannot lead to data races
			return true;
		}
		if (lrVal instanceof HeapLValue) {
			final Expression address = ((HeapLValue) lrVal).getAddress();
			return address instanceof IdentifierExpression
					&& ((IdentifierExpression) address).getIdentifier().startsWith(SFO.FUNCTION_ADDRESS);
		}
		if (!(lrVal instanceof LocalLValue)) {
			return false;
		}

		// Non-heap LHS whose root variable is not global do not admit races. Even when passed to other threads, they
		// are either copied (primitives, structs) or passed via pointer (but then they must be on heap!).
		final VariableLHS varLhs = getRootLhs(((LocalLValue) lrVal).getLhs());
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

	private static VariableLHS getRootLhs(LeftHandSide lhs) {
		while (!(lhs instanceof VariableLHS)) {
			if (lhs instanceof StructLHS) {
				lhs = ((StructLHS) lhs).getStruct();
			} else if (lhs instanceof ArrayLHS) {
				lhs = ((ArrayLHS) lhs).getArray();
			} else {
				throw new IllegalArgumentException("unknown type of LHS: " + lhs);
			}
		}
		return (VariableLHS) lhs;
	}

	private LeftHandSide[] getRaceLhs(final ILocation loc, final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;
			final LeftHandSide raceLhs = mMemoryHandler.getMemoryRaceArrayLhs(loc);

			final LeftHandSide[] lhs = new LeftHandSide[getTypeSize(loc, hlv.getUnderlyingType())];
			for (int i = 0; i < lhs.length; ++i) {
				// TODO For better performance, use memory model resolution to have fewer LHS here
				final Expression ptrPlusI =
						mMemoryHandler.addIntegerConstantToPointer(loc, hlv.getAddress(), BigInteger.valueOf(i));
				lhs[i] = ExpressionFactory.constructNestedArrayLHS(loc, raceLhs, new Expression[] { ptrPlusI });
			}
			return lhs;
		}
		if (lrVal instanceof LocalLValue) {
			return new LeftHandSide[] { getRaceIndicatorLhs(loc, (LocalLValue) lrVal) };
		}
		throw new UnsupportedOperationException();
	}

	private Stream<Expression> getRaceExpressions(final ILocation loc, final LRValue lrVal) {
		return Arrays.stream(getRaceLhs(loc, lrVal)).map(CTranslationUtil::convertLhsToExpression);
	}

	private int getTypeSize(final ILocation loc, final CType type) {
		final Expression operandTypeByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, type);
		return mTypeSizes.extractIntegerValue(operandTypeByteSizeExp, mTypeSizeComputer.getSizeT()).intValueExact();
	}

	private LeftHandSide getRaceIndicatorLhs(final ILocation loc, final LocalLValue lval) {
		return createRaceIndicatorLhs(loc, lval.getLhs());
	}

	private LeftHandSide createRaceIndicatorLhs(final ILocation loc, final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			final String name = "#race" + ((VariableLHS) lhs).getIdentifier();
			final VariableLHS raceLhs = new VariableLHS(loc, getRaceIndicatorType(lhs.getType()), name,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
			assert mRaceIndicators.getOrDefault(name, (BoogieType) raceLhs.getType())
					.equals(raceLhs.getType()) : "Ambiguous types for " + name + ": " + mRaceIndicators.get(name)
							+ " vs. " + raceLhs.getType();
			mRaceIndicators.put(name, (BoogieType) raceLhs.getType());
			return raceLhs;
		}

		if (!SUPPORT_ARRAY_STRUCT_LHS) {
			throw new UnsupportedOperationException(UNSUPPORTED_MSG);
		}

		if (lhs instanceof ArrayLHS) {
			final LeftHandSide raceLhs = createRaceIndicatorLhs(loc, ((ArrayLHS) lhs).getArray());
			return ExpressionFactory.constructNestedArrayLHS(loc, raceLhs, ((ArrayLHS) lhs).getIndices());
		}

		if (lhs instanceof StructLHS) {
			final LeftHandSide raceLhs = createRaceIndicatorLhs(loc, ((StructLHS) lhs).getStruct());
			return ExpressionFactory.constructStructAccessLhs(loc, raceLhs, ((StructLHS) lhs).getField());
		}

		throw new UnsupportedOperationException("Cannot detect races for " + lhs);
	}

	private BoogieType getRaceIndicatorType(final IBoogieType type) {
		if (type instanceof BoogiePrimitiveType || type.equals(mTypeHandler.getBoogiePointerType())) {
			return getBoolType();
		}
		if (type instanceof BoogieArrayType) {
			final BoogieArrayType arrType = (BoogieArrayType) type;
			assert arrType.getNumPlaceholders() == 0;
			final BoogieType[] indices = new BoogieType[arrType.getIndexCount()];
			for (int i = 0; i < indices.length; ++i) {
				indices[i] = arrType.getIndexType(i);
			}
			return BoogieType.createArrayType(0, indices, getRaceIndicatorType(arrType.getValueType()));
		}
		if (type instanceof BoogieStructType) {
			final BoogieStructType strType = (BoogieStructType) type;
			final BoogieType[] fieldTypes =
					Arrays.stream(strType.getFieldTypes()).map(this::getRaceIndicatorType).toArray(BoogieType[]::new);
			return BoogieType.createStructType(strType.getFieldIds(), fieldTypes);
		}
		throw new UnsupportedOperationException("Cannot detect races for values of type " + type);
	}

	private Expression wrapRaceIndicatorValue(final ILocation loc, final Expression value, final IBoogieType type) {
		if (type instanceof BoogiePrimitiveType || type.equals(mTypeHandler.getBoogiePointerType())) {
			return value;
		}
		if (type instanceof BoogieArrayType) {
			return ConstantArrayUtil.getConstantArray(mFunDecl, loc, (BoogieArrayType) type, value);
		}
		if (type instanceof BoogieStructType) {
			final BoogieStructType strType = (BoogieStructType) type;
			final Expression[] fieldValues = Arrays.stream(strType.getFieldTypes())
					.map(t -> wrapRaceIndicatorValue(loc, value, t)).toArray(Expression[]::new);
			return ExpressionFactory.constructStructConstructor(loc, strType.getFieldIds(), fieldValues);
		}
		throw new UnsupportedOperationException("Cannot detect races for values of type " + type);
	}

	public Collection<Declaration> declareRaceCheckingInfrastructure(final ILocation loc) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		decl.add(constructMemoryRaceArrayDeclaration(loc));

		for (final Map.Entry<String, BoogieType> raceVar : mRaceIndicators.entrySet()) {
			final VarList vlV = new VarList(loc, new String[] { raceVar.getKey() }, raceVar.getValue().toASTType(loc));
			decl.add(new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV }));
		}
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
