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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
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

/**
 * Creates data race checking instrumentation code for read and write accesses to global variables and heap memory.
 *
 * Our data race instrumentation is described in the SV-COMP'23 paper "Ultimate Taipan and Race Detection in Ultimate"
 * <https://doi.org/10.1007/978-3-031-30820-8_40>.
 *
 * In short, for every memory location, our instrumentation introduces an auxiliary boolean variable (called a "race
 * indicator") which is modified whenever the location is written to or read from. The instrumentation furthermore
 * introduces assert statements that can be violated if (and only if) there is a concurrent racing access to the same
 * memory location.
 */
public final class DataRaceChecker {
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;
	private final ITypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeComputer;
	private final TypeSizes mTypeSizes;
	private final ProcedureManager mProcedureManager;
	private final FunctionDeclarations mFunDecl;

	private final Map<String, BoogieType> mRaceIndicators = new HashMap<>();

	public DataRaceChecker(final AuxVarInfoBuilder auxVarInfoBuilder, final MemoryHandler memoryHandler,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeComputer, final TypeSizes typeSizes,
			final ProcedureManager procMan, final FunctionDeclarations funDecl) {
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mMemoryHandler = memoryHandler;
		mTypeHandler = typeHandler;
		mTypeSizeComputer = typeSizeComputer;
		mTypeSizes = typeSizes;
		mProcedureManager = procMan;
		mFunDecl = funDecl;
	}

	/**
	 * Adds a data race check appropriate for read accesses.
	 *
	 * @param erb
	 *            An {@link ExpressionResultBuilder} to which the data race check statements are added
	 * @param loc
	 *            the location of the read
	 * @param lrVal
	 *            The value being read
	 */
	@SuppressWarnings({ "unused" })
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

	/**
	 * Adds a data race check appropriate for write accesses.
	 *
	 * @param erb
	 *            An {@link ExpressionResultBuilder} to which the data race check statements and declarations are added
	 * @param loc
	 *            the location of the write
	 * @param lrVal
	 *            The value being written
	 */
	@SuppressWarnings("unused")
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
		switch (lhs) {
		case final VariableLHS variable:
			return ImmutableList.singleton(variable.getIdentifier());

		case final StructLHS struct:
			final ImmutableList<String> prefix = getAccessPath(struct.getStruct());
			if (prefix == null) {
				return null;
			}
			return new ImmutableList<>(struct.getField(), prefix);

		case final ArrayLHS array:
			return null;
		}
	}

	@SuppressWarnings("deprecation")
	private static boolean isRaceImpossible(final LRValue lrVal) {
		if (lrVal.getCType().isAtomic()) {
			// Atomic types cannot lead to data races
			return true;
		}
		if (lrVal instanceof final HeapLValue hlv) {
			return hlv.getAddress() instanceof final IdentifierExpression id
					&& id.getIdentifier().startsWith(SFO.FUNCTION_ADDRESS);
		}
		if (!(lrVal instanceof final LocalLValue llv)) {
			return false;
		}

		// Non-heap LHS whose root variable is not global do not admit races. Even when passed to other threads, they
		// are either copied (primitives, structs) or passed via pointer (but then they must be on heap!).
		final VariableLHS varLhs = getRootLhs(llv.getLhs());
		return switch (varLhs.getDeclarationInformation().getStorageClass()) {
		case LOCAL, IMPLEMENTATION_INPARAM, IMPLEMENTATION_OUTPARAM, PROC_FUNC -> true;
		case GLOBAL, IMPLEMENTATION, PROC_FUNC_INPARAM, PROC_FUNC_OUTPARAM, QUANTIFIED -> false;
		};
	}

	private static VariableLHS getRootLhs(final LeftHandSide lhs) {
		return switch (lhs) {
		case final StructLHS struct -> getRootLhs(struct.getStruct());
		case final ArrayLHS array -> getRootLhs(array.getArray());
		case final VariableLHS variable -> variable;
		};
	}

	private LeftHandSide[] getRaceLhs(final ILocation loc, final LRValue lrVal) {
		if (lrVal instanceof final HeapLValue hlv) {
			final LeftHandSide raceLhs = mMemoryHandler.getMemoryRaceArrayLhs(loc);

			final LeftHandSide[] lhs = new LeftHandSide[getTypeSize(loc, hlv.getUnderlyingType())];
			for (int i = 0; i < lhs.length; ++i) {
				// TODO For better performance, use Memory Structure resolution to have fewer LHS here
				final Expression ptrPlusI =
						mMemoryHandler.addIntegerConstantToPointer(loc, hlv.getAddress(), BigInteger.valueOf(i));
				lhs[i] = ExpressionFactory.constructNestedArrayLHS(loc, raceLhs, new Expression[] { ptrPlusI });
			}
			return lhs;
		}
		if (lrVal instanceof final LocalLValue llv) {
			return new LeftHandSide[] { getRaceIndicatorLhs(loc, llv) };
		}
		throw new UnsupportedOperationException();
	}

	private Stream<Expression> getRaceExpressions(final ILocation loc, final LRValue lrVal) {
		return Arrays.stream(getRaceLhs(loc, lrVal)).map(CTranslationUtil::convertLhsToExpression);
	}

	private int getTypeSize(final ILocation loc, final ICType type) {
		final Expression operandTypeByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, type);
		return mTypeSizes.extractIntegerValue(operandTypeByteSizeExp, mTypeSizeComputer.getSizeT()).intValueExact();
	}

	private LeftHandSide getRaceIndicatorLhs(final ILocation loc, final LocalLValue lval) {
		return createRaceIndicatorLhs(loc, lval.getLhs());
	}

	private LeftHandSide createRaceIndicatorLhs(final ILocation loc, final LeftHandSide lhs) {
		switch (lhs) {
		case final VariableLHS variable:
			final String name = "#race" + variable.getIdentifier();
			final VariableLHS raceLhs = new VariableLHS(loc, getRaceIndicatorType(variable.getType()), name,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
			assert mRaceIndicators.getOrDefault(name, (BoogieType) raceLhs.getType()).equals(raceLhs.getType())
					: "Ambiguous types for " + name + ": " + mRaceIndicators.get(name) + " vs. " + raceLhs.getType();
			mRaceIndicators.put(name, (BoogieType) raceLhs.getType());
			return raceLhs;

		case final ArrayLHS array:
			final LeftHandSide arrayRaceLhs = createRaceIndicatorLhs(loc, array.getArray());
			return ExpressionFactory.constructNestedArrayLHS(loc, arrayRaceLhs, array.getIndices());

		case final StructLHS struct:
			final LeftHandSide structRaceLhs = createRaceIndicatorLhs(loc, struct.getStruct());
			return ExpressionFactory.constructStructAccessLhs(loc, structRaceLhs, struct.getField());
		}
	}

	private BoogieType getRaceIndicatorType(final IBoogieType type) {
		if (type instanceof BoogiePrimitiveType || type.equals(mTypeHandler.getBoogiePointerType())) {
			return getBoolType();
		}
		if (type instanceof final BoogieArrayType arrType) {
			assert arrType.getNumPlaceholders() == 0;
			final BoogieType[] indices = new BoogieType[arrType.getIndexCount()];
			for (int i = 0; i < indices.length; ++i) {
				indices[i] = arrType.getIndexType(i);
			}
			return BoogieType.createArrayType(0, indices, getRaceIndicatorType(arrType.getValueType()));
		}
		if (type instanceof final BoogieStructType strType) {
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
		if (type instanceof final BoogieArrayType arrType) {
			return ConstantArrayUtil.getConstantArray(mFunDecl, loc, arrType, value);
		}
		if (type instanceof final BoogieStructType strType) {
			final Expression[] fieldValues = Arrays.stream(strType.getFieldTypes())
					.map(t -> wrapRaceIndicatorValue(loc, value, t)).toArray(Expression[]::new);
			return ExpressionFactory.constructStructConstructor(loc, strType.getFieldIds(), fieldValues);
		}
		throw new UnsupportedOperationException("Cannot detect races for values of type " + type);
	}

	/**
	 * Returns the declarations of auxiliary variables required by the data race checking instrumentation code.
	 *
	 * @param loc
	 *            The location to use for the declarations.
	 * @return the declarations of race indicator variables
	 */
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
