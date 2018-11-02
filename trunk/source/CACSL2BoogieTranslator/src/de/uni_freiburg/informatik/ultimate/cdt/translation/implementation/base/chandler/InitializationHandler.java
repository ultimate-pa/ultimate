/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.StringLiteralResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

/**
 * Generates Boogie code that models initializations that happen in the C program. Initializations may happen
 * implicitly, e.g., for static variables, or explicitly via an initializer.
 * <p>
 * The "uninitialized" case is not treated here (We havoc each variable at its initialization position, by default. That
 * is done somewhere else.).
 * <p>
 * C11 draft, 6.7.9.10: (concerning) default initialization) If an object that has automatic storage duration is not
 * initialized explicitly, its value is indeterminate. If an object that has static or thread storage duration is not
 * initialized explicitly, then:
 * <li>if it has pointer type, it is initialized to a null pointer;
 * <li>if it has arithmetic type, it is initialized to (positive or unsigned) zero;
 * <li>if it is an aggregate, every member is initialized (recursively) according to these rules, and any padding is
 * initialized to zero bits;
 * <li>if it is a union, the first named member is initialized (recursively) according to these rules, and any padding
 * is initialized to zero bits;
 * <p>
 * Some other special cases mentioned in C11 draft, 6.7.9, mostly concerning designators:
 * <li>Unnamed fields of a struct are uninitialized after initialization with an initializer. However after
 * initialization with a fitting struct object identifier they are initialized according to the object.
 * <li>array designators may specify start points for the initialization of an array
 * <li>array designators must use constant expressions (6.6. : such expression can be evaluated at compile-time).
 * <li>array designators can lead to a cell being assigned twice, when they overlap
 * <li>struct designators may specify which field is initialized next, regardless of order in the initializer list
 * <li>struct and array designators can be mixed.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class InitializationHandler {

	private final MemoryHandler mMemoryHandler;

	private final ExpressionTranslation mExpressionTranslation;

	private final ITypeHandler mTypeHandler;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final TypeSizeAndOffsetComputer mTypeSetAndOffsetComputer;

	private final TypeSizes mTypeSizes;

	private final CHandler mCHandler;

	private final ExpressionResultTransformer mExprResultTransformer;

	public InitializationHandler(final MemoryHandler memoryHandler, final ExpressionTranslation expressionTranslation,
			final ProcedureManager procedureManager, final ITypeHandler typeHandler,
			final AuxVarInfoBuilder auxVarInfoBuilder, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final TypeSizes typeSizes, final CHandler chandler,
			final ExpressionResultTransformer exprResultTransformer) {
		mMemoryHandler = memoryHandler;
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeSetAndOffsetComputer = typeSizeAndOffsetComputer;
		mTypeSizes = typeSizes;
		mCHandler = chandler;
		mExprResultTransformer = exprResultTransformer;
	}

	/**
	 * Either an expression that is to be initialized is given (via a LeftHandSide). Or we return an ExpressionResult
	 * that has an LrValue that is initialized and that can then be assigned to something by the caller. (we might do
	 * both in the "on-heap" case)
	 *
	 * @param loc
	 * @param main
	 * @param lhsRaw
	 * @param targetCTypeRaw
	 *            The CType of the object that is to be initialized (required for conversions)
	 * @param initializerRaw
	 * @return
	 */
	public ExpressionResult initialize(final ILocation loc, final LeftHandSide lhsRaw, final CType targetCTypeRaw,
			final InitializerResult initializerRaw, final IASTNode hook) {

		final boolean onHeap;
		if (lhsRaw != null && lhsRaw instanceof VariableLHS) {
			onHeap = mCHandler.isHeapVar(((VariableLHS) lhsRaw).getIdentifier());
		} else {
			onHeap = false;
		}

		final LRValue lhs;
		if (onHeap) {
			// lhsRaw must be non-null at this point because of the above code that determined "onHeap"
			// IdentifierExpression idEx = new IdentifierExpression(loc, ((VariableLHS) lhsRaw).getIdentifier());
			final VariableLHS vlhs = (VariableLHS) lhsRaw;
			final IdentifierExpression idEx = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogiePointerType(), vlhs.getIdentifier(), vlhs.getDeclarationInformation());
			lhs = LRValueFactory.constructHeapLValue(mTypeHandler, idEx, targetCTypeRaw, null);
		} else {
			lhs = lhsRaw == null ? null : new LocalLValue(lhsRaw, targetCTypeRaw, null);
		}

		final InitializerInfo initializerInfo;
		if (initializerRaw != null) {
			/*
			 * C11 6.7.9.1 : the grammar for initializers cannot generate empty initializers
			 */
			if (initializerRaw.getRootExpressionResult() == null
					&& (initializerRaw.getList() == null || initializerRaw.getList().isEmpty())) {
				throw new IncorrectSyntaxException(loc, "Empty initializers are not allowed by the C standard.");
			}

			// construct an InitializerInfo from the InitializerResult
			initializerInfo = constructInitializerInfo(loc, initializerRaw, targetCTypeRaw, hook);
		} else {
			initializerInfo = null;
		}

		final ExpressionResultBuilder init = new ExpressionResultBuilder();
		final boolean nondet = initializerInfo != null && initializerInfo.isMakeNondeterministicInitialization();
		if (onHeap && !nondet && determineIfSophisticatedDefaultInit(targetCTypeRaw)) {
			// in the "sophisticated" case: make a default initialization of all array cells first
			final ExpressionResult defaultInit =
					makeDefaultOrNondetInitialization(loc, lhs, targetCTypeRaw, onHeap, false, hook);
			init.addAllExceptLrValue(defaultInit);
		}


		{
			final ExpressionResult mainInitCode = initRec(loc, targetCTypeRaw, initializerInfo, onHeap, lhs, true,
					hook);
			init.addAllExceptLrValue();
			init.setLrValue(mainInitCode.getLrValue());
		}
		return init.build();
	}

	/**
	 *
	 * @param loc
	 * @param targetCTypeRaw
	 * @param initInfoIfAny
	 * @param onHeap
	 * @param lhsIfAny
	 * @param outermostNestedArray see {@link #initCArray}, this flag is ignored, if targetCTypeRaw.getUnderlyingType
	 *           is not CArray
	 * @param hook
	 * @return
	 */
	private ExpressionResult initRec(final ILocation loc, final CType targetCTypeRaw,
			final InitializerInfo initInfoIfAny, final boolean onHeap, final LRValue lhsIfAny,
			final boolean outermostNestedArray, final IASTNode hook) {
		assert lhsIfAny == null || lhsIfAny.getCType().getUnderlyingType().equals(targetCTypeRaw.getUnderlyingType());
		assert !onHeap || lhsIfAny != null : "we need a start address for on-heap initialization";

		final CType targetCType = targetCTypeRaw.getUnderlyingType();

		if (initInfoIfAny == null) {
			// there is no initializer -- apply default initialization
			return makeDefaultOrNondetInitialization(loc, lhsIfAny, targetCType, onHeap, false, hook);
		}

		if (initInfoIfAny.isMakeNondeterministicInitialization()) {
			return makeNondetInitAndAddOverapprFromInitInfo(loc, initInfoIfAny, onHeap, lhsIfAny, targetCType, hook);
		}

		if (targetCType instanceof CPrimitive || targetCType instanceof CEnum || targetCType instanceof CPointer) {
			/*
			 * We are dealing with an initialization of a value with non-aggregate type.
			 */
			return initExpressionWithExpression(loc, lhsIfAny, onHeap, targetCType, initInfoIfAny, hook);
		} else if (targetCType instanceof CStructOrUnion) {
			// unions are handled along with structs here
			return initCStruct(loc, lhsIfAny, (CStructOrUnion) targetCType, initInfoIfAny, onHeap, hook);
		} else if (targetCType instanceof CArray) {
			return initCArray(loc, lhsIfAny, (CArray) targetCType, initInfoIfAny, onHeap,
					determineIfSophisticatedArrayInit(initInfoIfAny), outermostNestedArray, hook);
		} else {
			throw new UnsupportedOperationException("missing case for CType");
		}
	}

	protected ExpressionResult makeNondetInitAndAddOverapprFromInitInfo(final ILocation loc,
			final InitializerInfo initInfo, final boolean onHeap, final LRValue lhsIfAny, final CType targetCType,
			final IASTNode hook) {
		assert initInfo != null;
		assert initInfo.isMakeNondeterministicInitialization();

		final ExpressionResultBuilder init = new ExpressionResultBuilder();
		final ExpressionResult nondetinit =
				makeDefaultOrNondetInitialization(loc, lhsIfAny, targetCType, onHeap, true, hook);

		for (final Statement stm : nondetinit.getStatements()) {
			addOverApprToStatementAnnots(initInfo.getOverapprs(), stm);
		}

		init.addAllExceptLrValue(nondetinit);
		if (nondetinit.getLrValue() != null) {
			init.setLrValue(nondetinit.getLrValue());
		}
		init.addOverapprox(initInfo.getOverapprs());
		return init.build();
	}

	private ExpressionResult initExpressionWithExpression(final ILocation loc, final LRValue lhsIfAny,
			final boolean onHeap, final CType cType, final InitializerInfo initInfo, final IASTNode hook) {
		assert initInfo.hasExpressionResult();

		final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

		initializer.addAllExceptLrValue(initInfo.getExpressionResult());
		final RValue initializationValue = initInfo.getRValue();

		if (lhsIfAny != null) {
			// we have a lhs given, insert assignments such that the lhs is initialized
			final List<Statement> assigningStatements = makeAssignmentStatements(loc, lhsIfAny, onHeap, cType,
					initializationValue.getValue(), initInfo.getOverapprs(), hook);
			assigningStatements.forEach(stm -> addOverApprToStatementAnnots(initInfo.getOverapprs(), stm));
			initializer.addStatements(assigningStatements);
		} else {
			initializer.setLrValue(initializationValue);
		}

		return initializer.build();
	}

	private ExpressionResult initCStruct(final ILocation loc, final LRValue lhsIfAny, final CStructOrUnion cStructType,
			final InitializerInfo initInfo, final boolean onHeap, final IASTNode hook) {
		assert !initInfo.isMakeNondeterministicInitialization() : "catch nondeterministic case outside";

		if (initInfo.hasExpressionResult()) {
			// we are initializing through a struct-typed expression, not an initializer list
			return initExpressionWithExpression(loc, lhsIfAny, onHeap, cStructType, initInfo, hook);
		}
		// we have an initializer list

		// Builder to collect all the initialization code and possibly the result value.
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		// list that collects the initialization values for each field
		final ArrayList<LRValue> fieldLrValues = new ArrayList<>();

		final LRValue structBaseLhsToInitialize =
				obtainLhsToInitialize(loc, lhsIfAny, cStructType, onHeap, initialization);

		for (int i = 0; i < cStructType.getFieldCount(); i++) {

			if (CStructOrUnion.isUnion(cStructType) && onHeap && !initInfo.hasInitInfoForIndex(i)) {
				// in on-heap case: skip assignments to fields of unions except for the one that is really written
				continue;
			}

			final LRValue currentFieldLhs;
			if (onHeap) {
				assert lhsIfAny != null && lhsIfAny instanceof HeapLValue;
				currentFieldLhs = constructAddressForStructField(loc, (HeapLValue) structBaseLhsToInitialize, i, hook);
			} else if (lhsIfAny != null) {
				currentFieldLhs = CTranslationUtil.constructOffHeapStructAccessLhs(loc,
						(LocalLValue) structBaseLhsToInitialize, i);
			} else {
				currentFieldLhs = null;
			}

			final ExpressionResult currentFieldInitialization;
			{
				final CType currentFieldUnderlyingType = cStructType.getFieldTypes()[i].getUnderlyingType();
				final InitializerInfo currentFieldInitializerRawIfAny =
						initInfo.hasInitInfoForIndex(i) ? initInfo.getInitInfoForIndex(i) : null;

				if (CStructOrUnion.isUnion(cStructType) && !initInfo.hasInitInfoForIndex(i)) {
					assert !onHeap;
					currentFieldInitialization = makeDefaultOrNondetInitialization(loc, currentFieldLhs,
							currentFieldUnderlyingType, onHeap, true, hook);
				} else {
					// normal case intitalize recursively with or without intitializer..
					currentFieldInitialization = initRec(loc, currentFieldUnderlyingType,
							currentFieldInitializerRawIfAny, onHeap, currentFieldLhs, true, hook);
				}
			}
			// add the initialization code
			initialization.addAllExceptLrValue(currentFieldInitialization);

			if (currentFieldInitialization.getLrValue() != null) {
				fieldLrValues.add(currentFieldInitialization.getLrValue());
			}

			if (CStructOrUnion.isUnion(cStructType) && onHeap && initInfo.hasInitInfoForIndex(i)) {
				// only the first field of a union is initialized
				break;
			}
		}

		if (onHeap) {
			// nothing to do
		} else if (lhsIfAny != null) {
			// nothing to do
		} else {
			/*
			 * Build the Boogie StructConstructor that carries the initialization values. And assign it to the lhs we
			 * constructed for this purpose.
			 */
			final List<Expression> fieldValues =
					fieldLrValues.stream().map(fieldLrValue -> fieldLrValue.getValue()).collect(Collectors.toList());
			final StructConstructor initializationValue = ExpressionFactory.constructStructConstructor(loc,
					cStructType.getFieldIds(), fieldValues.toArray(new Expression[fieldValues.size()]));

			final AssignmentStatement assignment = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { ((LocalLValue) structBaseLhsToInitialize).getLhs() },
					new Expression[] { initializationValue });
			addOverApprToStatementAnnots(initInfo.getOverapprs(), assignment);
			initialization.addStatement(assignment);
		}
		return initialization.build();
	}

	/**
	 *
	 * @param loc
	 * @param lhsIfAny
	 * @param cArrayType
	 * @param initInfo
	 * @param onHeap
	 * @param sophisticated
	 * @param outermostInNestedArray true iff the array to be initialized is not nested inside another array
	 *              (reason for this flag: if we have a nested array, e.g., <code>int a[2][3]</code>, then we do the
	 *               default initialization in the "sophisticated initialization" case for the outermost array, in order
	 *               to minimize the number of statements required for initialization)
	 *               This is only relevant in the off-heap case.
	 * @param hook
	 * @return
	 */
	private ExpressionResult initCArray(final ILocation loc, final LRValue lhsIfAny, final CArray cArrayType,
			final InitializerInfo initInfo, final boolean onHeap, final boolean sophisticated,
			final boolean outermostInNestedArray, final IASTNode hook) {
		assert !initInfo.isMakeNondeterministicInitialization() : "catch nondeterministic case outside";

		/*
		 * Builder where we accumulate all initialization information (Boogie code + LRValue mostly).
		 */
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		// take over code from the (converted) initializer
		if (initInfo.hasExpressionResult()) {
			initialization.addAllExceptLrValue(initInfo.getExpressionResult());
		}

		/*
		 * On-heap: Obtain the start address HeapLValue for the array initialization.
		 *
		 * Off-heap: Obtain the array that we will assign to later. (Will be the lhs, if that is non-null, or some
		 * auxiliary variable)
		 */
		final LRValue arrayLhsToInitialize = obtainLhsToInitialize(loc, lhsIfAny, cArrayType, onHeap, initialization);

		/* Note: we had code for sophisticated default initialization here. This has been moved to initialize(..)
		 * because it is only done once per variable  TODO: update this comment*/
		if (!onHeap && sophisticated && outermostInNestedArray) {
			// in the "sophisticated" off heap case: make a default initialization of all array cells first
			final ExpressionResult defaultInit =
					makeDefaultOrNondetInitialization(loc, arrayLhsToInitialize, cArrayType, onHeap, false, hook);
			initialization.addAllExceptLrValue(defaultInit);
		}


		/*
		 * Iterate over all array indices and assign the corresponding array cell; In the sophisticated case, only cells
		 * explicitly mentioned by the initializer are updated here. Otherwise all cells are updated
		 */
		if (CTranslationUtil.isToplevelVarlengthArray(cArrayType, mTypeSizes, hook)) {
			throw new UnsupportedOperationException("handling varlength arrays not implemented for this case");
		}
		final int bound = CTranslationUtil.getConstantFirstDimensionOfArray(cArrayType, mTypeSizes, hook);

		for (int i = 0; i < bound; i++) {
			final InitializerInfo arrayIndexInitInfo;
			if (initInfo.hasInitInfoForIndex(i)) {
				arrayIndexInitInfo = initInfo.getInitInfoForIndex(i);
			} else {
				// setting this to null will make the recursive call return a default initialization
				arrayIndexInitInfo = null;
			}

			if (sophisticated && arrayIndexInitInfo == null) {
				// in the "sophisticated" case we have default-initialized all cells up front --> nothing to do here
				continue;
			}

			final int arrayIndex = i;

			final CType cellType = cArrayType.getValueType();

			final LRValue arrayCellLhs;

			if (onHeap) {
				/*
				 * initialize the array cell, if the value type is an aggregate type, this means, we have to initialize
				 * the "subcells"
				 */
				arrayCellLhs =
						constructAddressForArrayAtIndex(loc, (HeapLValue) arrayLhsToInitialize, arrayIndex, hook);
			} else {
				/*
				 * this expression result contains a value that holds the contents for the array cell at the current
				 * index (we don't give a leftHandSide to initVarRec, and use the value that is given to the
				 * ExpressionResult)
				 */

				// say we initialize multidimensional array a, build a lhs a[i] here (which still may have array type)
				arrayCellLhs = CTranslationUtil.constructArrayAccessLhs(loc, (LocalLValue) arrayLhsToInitialize,
						arrayIndex, mTypeSizes);

			}
			// generate and add code to initialize the array cell (and possibly its subcells)
			final ExpressionResult arrayIndexInitialization;

			arrayIndexInitialization = initRec(loc, cellType, arrayIndexInitInfo, onHeap, arrayCellLhs, false, hook);

			initialization.addAllExceptLrValue(arrayIndexInitialization);

		}

		return initialization.build();
	}

	private ExpressionResult makeDefaultOrNondetInitialization(final ILocation loc, final LRValue lhsIfAny,
			final CType cTypeRaw, final boolean onHeap, final boolean nondet, final IASTNode hook) {
		assert !onHeap || lhsIfAny != null : "for on-heap initialization we need a start address";

		final CType cType = cTypeRaw.getUnderlyingType();

		final boolean sophisticated = determineIfSophisticatedDefaultInit(cType);

		/*
		 * If one of the following conditions holds, we must have an lhs for initialization. <li> we initialize
		 * something on-heap (we need a start-address to assign to <li> we initialize an array
		 */
		if (!onHeap && !(cType instanceof CArray)) {
			return makeOffHeapDefaultOrNondetInitializationForType(loc, cType, sophisticated, (LocalLValue) lhsIfAny,
					nondet, hook);
		}
		// array case or on-heap case, using an lhs

		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		final LRValue lhsToInit = obtainLhsToInitialize(loc, lhsIfAny, cType, onHeap, initialization);

		if (onHeap) {
			final ExpressionResult defaultInit =
					makeOnHeapDefaultInitializationForType(loc, (HeapLValue) lhsToInit, cType, sophisticated, hook);
			initialization.addAllExceptLrValue(defaultInit);
			assert defaultInit.getLrValue() == null : "on-heap initialization does not need a return value";
		} else {
			final ExpressionResult defaultInit = makeOffHeapDefaultOrNondetInitializationForType(loc, cType,
					sophisticated, (LocalLValue) lhsToInit, nondet, hook);
			initialization.addAllExceptLrValue(defaultInit);
			if (defaultInit.getLrValue() != null) {
				assert lhsToInit == null;
				initialization.setLrValue(defaultInit.getLrValue());
			}
		}

		return initialization.build();
	}

	private ExpressionResult makeOnHeapDefaultInitializationForType(final ILocation loc, final HeapLValue baseAddress,
			final CType cTypeRaw, final boolean sophisticated, final IASTNode hook) {
		final CType cType = cTypeRaw.getUnderlyingType();
		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {
			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();
			final List<Statement> defaultInit = makeAssignmentStatements(loc, baseAddress, true, cType,
					getDefaultValueForSimpleType(loc, cType), Collections.emptyList(), hook);
			initialization.addStatements(defaultInit);
			return initialization.build();
		} else if (cType instanceof CStructOrUnion) {
			final CStructOrUnion cStructType = (CStructOrUnion) cType;

			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

			final String[] fieldIds = cStructType.getFieldIds();

			for (int i = 0; i < fieldIds.length; i++) {
				final HeapLValue fieldPointer = constructAddressForStructField(loc, baseAddress, i, hook);

				final ExpressionResult fieldDefaultInit = makeOnHeapDefaultInitializationForType(loc, fieldPointer,
						cStructType.getFieldTypes()[i], sophisticated, hook);

				initialization.addAllExceptLrValue(fieldDefaultInit);

				if (CStructOrUnion.isUnion(cType)) {
					// only the first field in the struct that we save for a union is initialized
					break;
				}
			}
			return initialization.build();
		} else if (cType instanceof CArray) {
			if (sophisticated) {
				return makeSophisticatedOnHeapDefaultInitializationForArray(loc, baseAddress, (CArray) cType);
			}
			return makeNaiveOnHeapDefaultInitializationForArray(loc, baseAddress, (CArray) cType, hook);
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	/**
	 *
	 * @param loc
	 * @param cTypeRaw
	 * @param sophisticated
	 * @param lhsToInitIfAny
	 * @param nondet
	 *            if this is true, a nondeterministic value is used for initialization otherwise the default value
	 * @return
	 */
	private ExpressionResult makeOffHeapDefaultOrNondetInitializationForType(final ILocation loc, final CType cTypeRaw,
			final boolean sophisticated, final LocalLValue lhsToInitIfAny, final boolean nondet, final IASTNode hook) {
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {

			final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

			final LRValue initializationValue;
			if (nondet) {
				final ExpressionResult auxvar = makeUnionAuxVarExpressionResult(loc, cType);
				initializer.addAllExceptLrValue(auxvar);
				initializationValue = auxvar.getLrValue();
			} else {
				initializationValue = new RValue(getDefaultValueForSimpleType(loc, cType), cType);
			}

			if (lhsToInitIfAny != null) {
				// we have a lhs given, insert assignments such that the lhs is initialized
				final List<Statement> assigningStatements = makeAssignmentStatements(loc, lhsToInitIfAny, false, cType,
						initializationValue.getValue(), Collections.emptyList(), hook);
				initializer.addStatements(assigningStatements);
			} else {
				initializer.setLrValue(initializationValue);
			}
			return initializer.build();
		} else if (cType instanceof CStructOrUnion) {
			final CStructOrUnion cStructType = (CStructOrUnion) cType;

			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

			final ArrayList<LRValue> fieldLrValues = new ArrayList<>();

			for (int i = 0; i < cStructType.getFieldCount(); i++) {

				final LocalLValue fieldLhs;
				{
					if (lhsToInitIfAny == null) {
						fieldLhs = null;
					} else {
						final String fieldName = cStructType.getFieldIds()[i];
						final LeftHandSide lhs =
								ExpressionFactory.constructStructAccessLhs(loc, lhsToInitIfAny.getLhs(), fieldName);
						fieldLhs = new LocalLValue(lhs, cStructType.getFieldTypes()[i], null);
					}
				}

				final ExpressionResult fieldDefaultInit;
				if (CStructOrUnion.isUnion(cType) && i != 0) {
					/*
					 * In case of a union, all fields not mentioned in the initializer are havocced, thus their default
					 * initialization is a fresh auxiliary variable. However there is one exception: the first field is
					 * default-inititalized.
					 */
					fieldDefaultInit = makeOffHeapDefaultOrNondetInitializationForType(loc,
							cStructType.getFieldTypes()[i], sophisticated, fieldLhs, true, hook);
				} else {
					fieldDefaultInit = makeOffHeapDefaultOrNondetInitializationForType(loc,
							cStructType.getFieldTypes()[i], sophisticated, fieldLhs, nondet, hook);
				}

				initialization.addAllExceptLrValue(fieldDefaultInit);
				fieldLrValues.add(fieldDefaultInit.getLrValue());
			}

			if (lhsToInitIfAny == null) {
				final List<Expression> fieldValues =
						fieldLrValues.stream().map(LRValue::getValue).collect(Collectors.toList());
				final StructConstructor initializationValue = ExpressionFactory.constructStructConstructor(loc,
						cStructType.getFieldIds(), fieldValues.toArray(new Expression[fieldValues.size()]));
				initialization.setLrValue(new RValue(initializationValue, cType));
			}

			return initialization.build();
		} else if (cType instanceof CArray) {
			/* In the off-heap case, sophisticated initialization for arrays (e.g. with constant arrays) is only
			 * applicable if the value type is simple, i.e., not a struct or union type. */
			if (sophisticated
					&& !(CTranslationUtil.getValueTypeOfNestedArray((CArray) cType) instanceof CStructOrUnion)) {
				return makeSophisticatedOffHeapDefaultInitializationForArray(loc, (CArray) cType, nondet);
			}
			return makeNaiveOffHeapDefaultOrNondetInitForArray(loc, (CArray) cType, lhsToInitIfAny, nondet, hook);
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	private ExpressionResult makeUnionAuxVarExpressionResult(final ILocation loc, final CType fieldType) {
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, fieldType, SFO.AUXVAR.NONDET);
		return new ExpressionResultBuilder().setLrValue(new RValue(auxVar.getExp(), fieldType))
				.addDeclaration(auxVar.getVarDec()).addAuxVar(auxVar)
				.addOverapprox(
						new Overapprox("initialize union -- havoccing a field without explictit " + "initializer", loc))
				.build();
	}

	private ExpressionResult makeNaiveOnHeapDefaultInitializationForArray(final ILocation loc,
			final HeapLValue baseAddress, final CArray cArrayType, final IASTNode hook) {
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		/* note this is different from {@link #makeNaiveOffHeapDefaultOrNondetInitForArray} in that we only take the
		 * outermost bound (so the List<List<Integer>> could be flattened to List<Integer>, but we keep it like this
		 * for keeping the similarity to the OffHeap variant) */
		final List<List<Integer>> allIndicesToInitialize =
				CrossProducts.crossProductOfSetsOfFirstNaturalNumbers(
						Collections.singletonList(
								CTranslationUtil.getConstantFirstDimensionOfArray(cArrayType, mTypeSizes, hook)));
		for (final List<Integer> arrayIndex : allIndicesToInitialize) {
			final HeapLValue arrayAccessLhs = constructAddressForArrayAtIndex(loc, baseAddress, arrayIndex, hook);

			final ExpressionResult arrayIndexInitialization =
					makeOnHeapDefaultInitializationForType(loc, arrayAccessLhs, cArrayType.getValueType(), false, hook);
			initialization.addAllExceptLrValue(arrayIndexInitialization);
		}
		return initialization.build();
	}

	private ExpressionResult makeSophisticatedOnHeapDefaultInitializationForArray(final ILocation loc,
			final HeapLValue baseAddress, final CArray cType) {
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();
		final List<Statement> initStatements =
				mMemoryHandler.getInitializationForOnHeapVariableOfAggregateOrUnionType(loc, baseAddress, cType);
		initialization.addStatements(initStatements);
		return initialization.build();
	}

	private ExpressionResult makeNaiveOffHeapDefaultOrNondetInitForArray(final ILocation loc, final CArray cArrayType,
			final LocalLValue lhsToInit, final boolean nondet, final IASTNode hook) {
		assert lhsToInit != null;

		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		final LocalLValue arrayLhsToInitialize = lhsToInit;

		CType innerMostValueType = cArrayType.getValueType().getUnderlyingType();
		while (innerMostValueType instanceof CArray) {
			innerMostValueType = ((CArray) innerMostValueType).getValueType().getUnderlyingType();
		}

		final List<List<Integer>> allIndicesToInitialize = CrossProducts.crossProductOfSetsOfFirstNaturalNumbers(
				CTranslationUtil.getConstantDimensionsOfArray(cArrayType, mTypeSizes, hook));
		for (final List<Integer> arrayIndex : allIndicesToInitialize) {

			final LocalLValue arrayAccessLhs =
					CTranslationUtil.constructArrayAccessLhs(loc, arrayLhsToInitialize, arrayIndex, mTypeSizes);

			final ExpressionResult arrayIndexInitialization = makeOffHeapDefaultOrNondetInitializationForType(loc,
					innerMostValueType, false, arrayAccessLhs, nondet, hook);
			initialization.addAllExceptLrValue(arrayIndexInitialization);
		}

		return initialization.build();
	}

	private ExpressionResult makeSophisticatedOffHeapDefaultInitializationForArray(final ILocation loc,
			final CArray cArrayType, final boolean nondet) {
		throw new UnsupportedOperationException("TODO"); // TODO
	}

	/**
	 * Side effect notice: This method may update the given initialization with declarations for an auxiliary variable
	 * and possibly set the LrValue.
	 */
	private LRValue obtainLhsToInitialize(final ILocation loc, final LRValue lhsIfAny, final CType cType,
			final boolean onHeap, final ExpressionResultBuilder initialization) {
		final LRValue arrayLhsToInitialize;
		if (onHeap) {
			assert lhsIfAny != null && lhsIfAny instanceof HeapLValue;
			arrayLhsToInitialize = lhsIfAny;
		} else {
			arrayLhsToInitialize = obtainLocalLValueToInitialize(loc, (LocalLValue) lhsIfAny, cType, initialization);
		}
		return arrayLhsToInitialize;
	}

	/**
	 *
	 * @param initialization
	 *            side effects on this parameter: is updated with the necessary declaration and the returned LocalLValue
	 *            is set as LrValue
	 */
	private LocalLValue obtainLocalLValueToInitialize(final ILocation loc, final LocalLValue lhsIfAny,
			final CType cType, final ExpressionResultBuilder initialization) {
		final LocalLValue arrayLhsToInitialize;
		if (lhsIfAny != null) {
			arrayLhsToInitialize = lhsIfAny;
		} else {
			// we need an auxiliary variable for the array to be the value of the ExpressionResult we return.
			arrayLhsToInitialize = obtainAuxVarLocalLValue(loc, cType, initialization);
		}
		return arrayLhsToInitialize;
	}

	/**
	 * @param initialization
	 *            side effects on this parameter: is updated with the necessary declaration and the returned LocalLValue
	 *            is set as LrValue
	 */
	private LocalLValue obtainAuxVarLocalLValue(final ILocation loc, final CType cType,
			final ExpressionResultBuilder initialization) {
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType);
		initialization.addDeclaration(auxVar.getVarDec());
		initialization.addAuxVar(auxVar);
		final LocalLValue arrayLhsToInitialize = new LocalLValue(auxVar.getLhs(), cType, null);
		initialization.setLrValue(arrayLhsToInitialize);
		return arrayLhsToInitialize;
	}

	/**
	 * Returns a call to the special array initialization procedure. ("off-heap" case) This procedure returns an array
	 * with the given signature where all cells within the given ranges have been initialized to the default value for
	 * the given value type.
	 *
	 * (Whether the initialization procedure will initialize cells beyond these ranges may vary between different
	 * implementations of that procedure.)
	 *
	 * @param lhs
	 *            the variable that the return value of the initialization procedure should be assigned to
	 * @param dimensions
	 *            the dimensions of the C array to initialize, this specifies both the index types (should be integer)
	 *            and the ranges for each array dimension.
	 * @param valueType
	 *            the type that the entries in the innermost arrays have
	 * @return
	 */
	private Statement getInitializerArrayCall(final LocalLValue lhs, final CArray arrayType) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Returns a call to the special array initialization procedure. ("on-heap" case) The initialization procedure takes
	 * as arguments a memory address and signature and range information for an array. The procedure ensures that after
	 * it has been called all the memory cells belonging to the given array and ranges have been initialized to the
	 * default value.
	 *
	 * (Whether the initialization procedure will initialize cells beyond these ranges may vary between different
	 * implementations of that procedure.)
	 *
	 * @param startAddress
	 * @param dimensions
	 * @param valueType
	 * @return
	 */
	private Statement getOnHeapArrayInitializationCall(final Expression startAddress, final CArray arrayType) {
		// TODO Auto-generated method stub
		return null;
	}

	private static void addOverApprToStatementAnnots(final Collection<Overapprox> overappr, final Statement stm) {
		if (overappr == null) {
			return;
		}
		for (final Overapprox overapprItem : overappr) {
			overapprItem.annotate(stm);
		}
	}

	public List<Declaration> declareInitializationInfrastructure(final IDispatcher main, final ILocation loc) {
		return Collections.emptyList();
	}

	/**
	 * Construct assignment statements that make sure that "lhs" gets the value "initializationValue".
	 */
	private List<Statement> makeAssignmentStatements(final ILocation loc, final LRValue lhs, final boolean onHeap,
			final CType cType, final Expression initializationValue, final Collection<Overapprox> overAppr,
			final IASTNode hook) {
		assert lhs != null;

		List<Statement> assigningStatements;
		if (onHeap) {
			assigningStatements =
					mMemoryHandler.getWriteCall(loc, (HeapLValue) lhs, initializationValue, cType, true, hook);
		} else {
			final AssignmentStatement assignment = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { ((LocalLValue) lhs).getLhs() }, new Expression[] { initializationValue });
			addOverApprToStatementAnnots(overAppr, assignment);
			assigningStatements = Collections.singletonList(assignment);
		}
		return assigningStatements;
	}

	private Expression getDefaultValueForSimpleType(final ILocation loc, final CType cTypeRaw) {
		final CType cType = cTypeRaw.getUnderlyingType();
		if (cType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) cType;
			switch (cPrimitive.getGeneralType()) {
			case INTTYPE:
				return mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ZERO);
			case FLOATTYPE:
				return mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive, BigDecimal.ZERO);
			case VOID:
				throw new AssertionError("cannot initialize something that has type void");
			default:
				throw new AssertionError("unknown category of type");
			}
		} else if (cType instanceof CEnum) {
			return mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO);
		} else if (cType instanceof CPointer) {
			return mExpressionTranslation.constructNullPointer(loc);
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	/**
	 * Determines which kind of initialization code we want to generate. There are two variants
	 * <li>"naive": We generate a sequence of assignments that initialize each field of the aggregate type object.
	 * <li>"sophisticated": We first initialize the whole object to default values and then insert assignments that
	 * initialize the fields that are explicitly mentioned by the initializer. The first step may be performed in
	 * different ways, for instance by while loops, or by using special SMT default arrays.
	 * <p>
	 * Some criteria for when to choose which:
	 * <li>when "most" of the initialized values are initialized explicitly, we choose "naive", for some threshold
	 * <li>variable length arrays need "sophisticated"
	 *
	 * @param initializerIfAny
	 * @return true iff sophisticated initialization should be applied
	 */
	private boolean determineIfSophisticatedArrayInit(final InitializerInfo initInfoIfAny) {
		// TODO implement some heuristics
//		return false;
		return true;
	}

	/**
	 * For the given type. Determine if we want to make a sophisticated or a naive initialization. See also
	 * {@link determineIfSophisticatedArrayInit}.
	 *
	 * @param targetCType
	 * @return
	 */
	private boolean determineIfSophisticatedDefaultInit(final CType targetCType) {
		// TODO implement some heuristics
//		return false;
		return true;
	}

	public HeapLValue constructAddressForArrayAtIndex(final ILocation loc, final HeapLValue arrayBaseAddress,
			final List<Integer> arrayIndex, final IASTNode hook) {
		final CArray cArrayType = (CArray) arrayBaseAddress.getCType().getUnderlyingType();

		final List<Integer> arrayBounds = CTranslationUtil.getConstantDimensionsOfArray(cArrayType, mTypeSizes, hook);

		Integer product = 0;
		for (int i = 0; i < arrayIndex.size(); i++) {
			final int factor = i == arrayIndex.size() - 1 ? 1 : arrayBounds.get(i + 1);
			product = product + factor * arrayIndex.get(i);
		}
		final CPrimitive sizeT = mTypeSetAndOffsetComputer.getSizeT();

		final Expression flatCellNumber =
				mTypeSizes.constructLiteralForIntegerType(loc, sizeT, new BigInteger(product.toString()));

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(arrayBaseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(arrayBaseAddress.getAddress(), loc);
		final Expression cellOffset = mMemoryHandler.multiplyWithSizeOfAnotherType(loc, cArrayType.getValueType(),
				flatCellNumber, sizeT, hook);
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerOffset, sizeT, cellOffset, sizeT);
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);

		return LRValueFactory.constructHeapLValue(mTypeHandler, newPointer, cArrayType.getValueType(), null);
	}

	public HeapLValue constructAddressForArrayAtIndex(final ILocation loc, final HeapLValue arrayBaseAddress,
			final Integer arrayIndex, final IASTNode hook) {
		final CArray cArrayType = (CArray) arrayBaseAddress.getCType().getUnderlyingType();

		final CPrimitive pointerComponentType = mExpressionTranslation.getCTypeOfPointerComponents();

		final Expression flatCellNumber = mTypeSizes.constructLiteralForIntegerType(loc, pointerComponentType,
				new BigInteger(arrayIndex.toString()));

		/* do a conversion so the expression has boogie pointer type */
		final RValue addressRVal = arrayBaseAddress.getAddressAsPointerRValue(mTypeHandler.getBoogiePointerType());
		// final Expression pointerBase = MemoryHandler.getPointerBaseAddress(arrayBaseAddress.getAddress(), loc);
		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(addressRVal.getValue(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(addressRVal.getValue(), loc);

		final CType cellType = cArrayType.getValueType();

		final Expression cellOffset =
				mMemoryHandler.multiplyWithSizeOfAnotherType(loc, cellType, flatCellNumber, pointerComponentType, hook);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerOffset, pointerComponentType, cellOffset, pointerComponentType);

		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);

		return LRValueFactory.constructHeapLValue(mTypeHandler, newPointer, cellType, null);
	}

	public HeapLValue constructAddressForStructField(final ILocation loc, final HeapLValue baseAddress,
			final int fieldIndex, final IASTNode hook) {
		final CStructOrUnion cStructType = (CStructOrUnion) baseAddress.getCType().getUnderlyingType();

		final CPrimitive sizeT = mTypeSetAndOffsetComputer.getSizeT();

		final Expression fieldOffset =
				mTypeSetAndOffsetComputer.constructOffsetForField(loc, cStructType, fieldIndex, hook);

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(baseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(baseAddress.getAddress(), loc);
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerOffset, sizeT, fieldOffset, sizeT);
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);

		return LRValueFactory.constructHeapLValue(mTypeHandler, newPointer, cStructType.getFieldTypes()[fieldIndex],
				null);
	}

	/**
	 * Converts a given InitializerResult to an InitializerInfo with respect to a given target CType.
	 *
	 * The target CType is the CType of the C object that will be initialized with the initializer that the
	 * InitializerResult has been generated from. Conceptually, the target CType is important because conversions may
	 * need to be applied according to it (e.g. a "0" may become the NULL pointer), and designated initializers may need
	 * to be reordered according to the field names of a target CStruct type.
	 *
	 * @param initializerResult
	 * @param targetCType
	 */
	public InitializerInfo constructInitializerInfo(final ILocation loc, final InitializerResult initializerResult,
			final CType targetCTypeRaw, final IASTNode hook) {
		final CType targetCType = targetCTypeRaw.getUnderlyingType();

		if (initializerResult.hasRootExpressionResult()) {
			/*
			 * We are initializing through an (possibly aggregate-type) expression (not through a list of expressions).
			 */

			if (initializerResult.getRootExpressionResult() instanceof StringLiteralResult
					&& targetCTypeRaw instanceof CArray) {
				/*
				 * Case like 'char a[] = "bla"' in C, initialization would copy the char array contents to a position on
				 * the stack we create an InitializerInfo that corresponds to the initializer { 'b', 'l', 'a', '\0' }.
				 * (For this purpose, StringLiteralResult holds the original string contents.)
				 */

				final StringLiteralResult slr = (StringLiteralResult) initializerResult.getRootExpressionResult();

				final List<Overapprox> overapproxList;
				if (slr.overApproximatesLongStringLiteral()) {
					final Overapprox overapprox = new Overapprox("large string literal", loc);
					overapproxList = new ArrayList<>();
					overapproxList.add(overapprox);
					return new InitializerInfo(overapprox);
				}
				// make the list (in our case a map because we support
				// sparse lists in other cases)
				final Map<Integer, InitializerInfo> indexToInitInfo = new HashMap<>();
				for (int i = 0; i < slr.getLiteralString().getByteValues().size(); i++) {
					final CPrimitive charCType = new CPrimitive(CPrimitives.CHAR);
					final Expression charLitExp = mTypeSizes.constructLiteralForIntegerType(loc, charCType,
							slr.getLiteralString().getByteValues().get(i));
					final ExpressionResult charResult =
							new ExpressionResultBuilder().setLrValue(new RValue(charLitExp, charCType)).build();
					indexToInitInfo.put(i, new InitializerInfo(charResult, Collections.emptyList()));
				}
				return new InitializerInfo(indexToInitInfo, Collections.emptyList());
			} else if (initializerResult.getRootExpressionResult() instanceof StringLiteralResult
					&& targetCTypeRaw instanceof CPointer) {
				/*
				 * case like 'char *a = "bla"' --> initialization will make the variable'a' point to the special
				 * read-only memory area for strings. There is already code in the StringLiteralResult for this.
				 *
				 * We use this code for a global declaration and code in Ultimate.init() (currently the field auxVars
				 * has entries, but they are not needed and may be removed in the future) The result we return here will
				 * only contain the RValue.
				 */
				final StringLiteralResult exprResult = (StringLiteralResult) convertInitResultWithExpressionResult(loc,
						targetCType, initializerResult, hook);

				assert exprResult.getDeclarations().isEmpty() : "the declarations necessary for a StringLiteral "
						+ " should be registered in StaticObjectsHandler directly (because the need to be global"
						+ "boogie declarations)";
				assert exprResult.getStatements().isEmpty() : "the statements necessary for a StringLiteral "
						+ " should be registered in StaticObjectsHandler directly (because the need to be global"
						+ "boogie declarations)";

				final ExpressionResult onlyRValueExprResult = new ExpressionResultBuilder()
						.setLrValue(exprResult.getLrValue()).addOverapprox(exprResult.getOverapprs()).build();

				return new InitializerInfo(onlyRValueExprResult, Collections.emptyList());
			} else {
				/*
				 * or case like "struct s s1 = s2;", make initializerInfo with one ExpressionResult
				 */
				final ExpressionResult converted =
						convertInitResultWithExpressionResult(loc, targetCType, initializerResult, hook);
				return new InitializerInfo(converted, Collections.emptyList());
			}
		}

		if (targetCType instanceof CArray || targetCType instanceof CStructOrUnion) {
			// // aggregate or union type
			return constructIndexToInitInfo(loc, initializerResult.getList(), targetCType, hook);
			// } else if (targetCType instanceof CStruct) {
			// // target type is a struct or a union type
			// return constructArrayIndexToInitInfo(loc, main, initializerResult.getList(), targetCType);
		}
		// do the necessary conversions
		final Deque<InitializerResult> ad = new ArrayDeque<>(initializerResult.getList());
		final InitializerResult first = ad.pollFirst();

		final ExpressionResult expressionResultSwitched =
				convertInitResultWithExpressionResult(loc, targetCType, first, hook);

		return new InitializerInfo(expressionResultSwitched, new ArrayList<>(ad));
	}

	protected ExpressionResult convertInitResultWithExpressionResult(final ILocation loc, final CType targetCType,
			final InitializerResult first, final IASTNode hook) {

		final ExpressionResult er = first.getRootExpressionResult();
		final ExpressionResult expressionResultSwitched = mExprResultTransformer
				.makeRepresentationReadyForConversionAndRexBoolToIntIfNecessary(er, mCHandler, loc, targetCType, hook);

		// TODO: 2018-09-05 Matthias: The following workaround may now be not required any more.
		// 2017-11-19 Matthias: introduced workaround to omit conversion
		if (expressionResultSwitched.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
			// omit conversion
			return expressionResultSwitched;
		}
		return mExprResultTransformer.convert(loc, expressionResultSwitched, targetCType);

	}

	private InitializerInfo constructIndexToInitInfo(final ILocation loc,
			final List<InitializerResult> initializerResults, final CType targetCType, final IASTNode hook) {
		assert targetCType instanceof CArray || targetCType instanceof CStructOrUnion;

		final Map<Integer, InitializerInfo> indexInitInfos = new HashMap<>();

		Deque<InitializerResult> rest = new ArrayDeque<>(initializerResults);

		final int bound;
		CType cellType = null;
		{
			if (targetCType instanceof CArray) {
				cellType = ((CArray) targetCType).getValueType();
				bound = CTranslationUtil.getConstantFirstDimensionOfArray((CArray) targetCType, mTypeSizes, hook);
				if (CTranslationUtil.isToplevelVarlengthArray((CArray) targetCType, mTypeSizes, hook)) {
					throw new UnsupportedOperationException("varlenght not yet supported here");
				}
			} else {
				bound = ((CStructOrUnion) targetCType).getFieldCount();
			}
		}

		/*
		 * The currentCellIndex stands for the "current object" from the standard text. Designators may modify that
		 * index otherwise it just counts up.
		 */
		int currentCellIndex = -1;
		while (currentCellIndex < bound - 1 && !rest.isEmpty()) {
			if (rest.peekFirst().hasRootDesignator()) {
				assert targetCType instanceof CStructOrUnion : "array designators not yet supported and should not (yet)"
						+ " show up here";
				currentCellIndex = CTranslationUtil.findIndexOfStructField((CStructOrUnion) targetCType,
						rest.peekFirst().getRootDesignator());
			} else {
				currentCellIndex++;
			}

			if (targetCType instanceof CStructOrUnion) {
				cellType = ((CStructOrUnion) targetCType).getFieldTypes()[currentCellIndex];
			}

			/*
			 * C11 6.7.9.13 The initializer for a structure or union object that has automatic storage duration shall be
			 * either an initializer list as described below, or a single expression that has compatible structure or
			 * union type. In the latter case, the initial value of the object, including unnamed members, is that of
			 * the expression.
			 */
			if (rest.peekFirst().isInitializerList() || (
			// TODO: make a more general compatibility check, for example for array and pointer
			rest.peekFirst().hasRootExpressionResult() && TypeHandler.isCompatibleType(cellType,
					rest.peekFirst().getRootExpressionResult().getLrValue().getCType()))) {
				/*
				 * case "{", i.e. one more brace opens Then the cell is initialized with the list belonging to that
				 * brace (until the matching brace). No residue is taken over if too many elements are left.
				 *
				 * other case: first list entry has a compatible struct or union type
				 */

				final InitializerResult first = rest.pollFirst();
				final InitializerInfo cellInitInfo = constructInitializerInfo(loc, first, cellType, hook);

				indexInitInfos.put(currentCellIndex, cellInitInfo);
			} else {
				/*
				 * Case where the list starts with a value (or identifier, just not with a brace). Then the current list
				 * is handed down to the cell, and if anything is left after processing that cell we use it for the next
				 * cell.
				 */
				final InitializerResultBuilder restInitResultBuilder = new InitializerResultBuilder();
				rest.forEach(restInitResultBuilder::addChild);
				final InitializerInfo cellInitInfo =
						constructInitializerInfo(loc, restInitResultBuilder.build(), cellType, hook);
				indexInitInfos.put(currentCellIndex, cellInitInfo);
				rest = new ArrayDeque<>(cellInitInfo.getUnusedListEntries());
			}
		}
		return new InitializerInfo(indexInitInfos, new ArrayList<>(rest));
	}

	/**
	 * Represents all information that is needed to initialize a given target expression with a given initializer. Is
	 * generated from an InitializerResult together with the target expression's CType.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	static class InitializerInfo {

		private final ExpressionResult mExpressionResult;

		private final Collection<Overapprox> mOverApprs;

		private final Map<Integer, InitializerInfo> mElementInitInfos;

		/**
		 * If this flag is set, then everything that is initialized with this InitInfo gets a nondeterministic value.
		 */
		private final boolean mMakeNondeterministicInitialization;

		/**
		 * Used only during building the InitializerInfo. An inner initialization may leave over values for an outer
		 * initialization.
		 */
		private final List<InitializerResult> mUnusedListEntries;

		private InitializerInfo(final ExpressionResult expressionResult, final List<InitializerResult> rest) {
			assert expressionResult.getLrValue() == null
					|| expressionResult.getLrValue() instanceof RValue : "switch to RValue first!";
			mExpressionResult = expressionResult;
			mOverApprs = expressionResult.getOverapprs();
			mElementInitInfos = Collections.emptyMap();
			mUnusedListEntries = rest;
			mMakeNondeterministicInitialization = false;
		}

		public InitializerInfo(final Map<Integer, InitializerInfo> indexInitInfos, final List<InitializerResult> rest) {
			mExpressionResult = null;
			mOverApprs = Collections.emptyList();
			mElementInitInfos = indexInitInfos;
			mUnusedListEntries = rest;
			mMakeNondeterministicInitialization = false;
		}

		/**
		 * Creates an InitializerInfo that assigns nondeterministic values to every concerned object or subobject.
		 *
		 * @param overapprox
		 */
		public InitializerInfo(final Overapprox overapprox) {
			mExpressionResult = null;
			mOverApprs = Collections.singletonList(overapprox);
			mElementInitInfos = Collections.emptyMap();
			mUnusedListEntries = Collections.emptyList();
			mMakeNondeterministicInitialization = true;
		}

		private List<InitializerResult> getUnusedListEntries() {
			return Collections.unmodifiableList(mUnusedListEntries);
		}

		public boolean hasExpressionResult() {
			return mExpressionResult != null;
		}

		public RValue getRValue() {
			return (RValue) mExpressionResult.getLrValue();
		}

		public ExpressionResult getExpressionResult() {
			return mExpressionResult;
		}

		public Collection<Integer> getIndicesWithInitInfo() {
			return mElementInitInfos.keySet();
		}

		public boolean hasInitInfoForIndex(final Integer index) {
			return mElementInitInfos.containsKey(index);
		}

		public InitializerInfo getInitInfoForIndex(final Integer index) {
			assert mElementInitInfos.get(index) != null;
			return mElementInitInfos.get(index);
		}

		public Collection<Overapprox> getOverapprs() {
			return mOverApprs;
		}

		public boolean isMakeNondeterministicInitialization() {
			return mMakeNondeterministicInitialization;
		}

		@Override
		public String toString() {
			if (mExpressionResult != null) {
				return mExpressionResult.toString();
			}
			if (mElementInitInfos != null) {
				return mElementInitInfos.toString();
			}
			if (mMakeNondeterministicInitialization) {
				return "nondeterministic initinfo";
			}
			return "?";
		}
	}
}
