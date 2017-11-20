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

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

/**
 * Generates Boogie code that models initializations that happen in the C program.
 * Initializations may happen implicitly, e.g., for static variables, or explicitly via an initializer.
 * <p>
 * The "uninitialized" case is not treated here (We havoc each variable at its initialization position, by default.
 * That is done somewhere else.).
 * <p>
 * C11 draft, 6.7.9.10: (concerning) default initialization)
 * If an object that has automatic storage duration is not initialized explicitly, its value is
 * indeterminate. If an object that has static or thread storage duration is not initialized
 * explicitly, then:
 *  <li> if it has pointer type, it is initialized to a null pointer;
 *  <li> if it has arithmetic type, it is initialized to (positive or unsigned) zero;
 *  <li> if it is an aggregate, every member is initialized (recursively) according to these rules,
 *    and any padding is initialized to zero bits;
 *  <li> if it is a union, the first named member is initialized (recursively) according to these
 *    rules, and any padding is initialized to zero bits;
 * <p>
 * Some other special cases mentioned in C11 draft, 6.7.9, mostly concerning designators:
 *  <li> Unnamed fields of a struct are uninitialized after initialization with an initializer. However after
 *   initialization with a fitting struct object identifier they are initialized according to the object.
 *  <li> array designators may specify start points for the initialization of an array
 *  <li> array designators must use constant expressions (6.6. : such expression can be evaluated at compile-time).
 *  <li> array designators can lead to a cell being assigned twice, when they overlap
 *  <li> struct designators may specify which field is initialized next, regardless of order in the initializer list
 *  <li> struct and array designators can be mixed.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class InitializationHandler {

	private final FunctionHandler mFunctionHandler;

	private final StructHandler mStructHandler;

	private final MemoryHandler mMemoryHandler;

	private final AExpressionTranslation mExpressionTranslation;

	private boolean mDeclareArrayInitializationFunction;

	public InitializationHandler(final FunctionHandler functionHandler, final StructHandler structHandler,
			final MemoryHandler memoryHandler, final AExpressionTranslation expressionTranslation) {
		super();
		mFunctionHandler = functionHandler;
		mStructHandler = structHandler;
		mMemoryHandler = memoryHandler;
		mExpressionTranslation = expressionTranslation;
		mDeclareArrayInitializationFunction = false;
	}

	/**
	 *
	 *
	 * Either an expression that is to be initialized is given (via a LeftHandSide). Or we return an ExpressionResult
	 * that has an LrValue that is initialized and that can then be assigned to something by the caller.
	 * (we might do both in the "on-heap" case)
	 *
	 * @param loc
	 * @param main
	 * @param lhsRaw
	 * @param targetCTypeRaw The CType of the object that is to be initialized (required for conversions)
	 * @param initializerRaw
	 * @return
	 */
	public ExpressionResult initialize(final ILocation loc, final Dispatcher main, final LeftHandSide lhsRaw,
			final CType targetCTypeRaw, final InitializerResult initializerRaw) {

		boolean onHeap = false;
		if (lhsRaw != null && lhsRaw instanceof VariableLHS) {
			onHeap = ((CHandler) main.mCHandler).isHeapVar(((VariableLHS) lhsRaw).getIdentifier());
		}

		LRValue lhs = null;
		if (onHeap) {
			// lhsRaw must be non-null at this point because of the above code that determined "onHeap"
			lhs = new HeapLValue(new IdentifierExpression(loc, ((VariableLHS) lhsRaw).getIdentifier()), targetCTypeRaw);
		} else {
			lhs = lhsRaw == null ? null : new LocalLValue(lhsRaw, targetCTypeRaw);
		}

		final InitializerInfo initializerInfo;
		if (initializerRaw != null) {
			// construct an InitializerInfo from the InitializerResult
			initializerInfo = InitializerInfo.constructInitializerInfo(loc, main,
//					initializerRaw.isInitializerList() ? initializerRaw.getList() : Collections.singletonList(initializerRaw),
					initializerRaw,
					targetCTypeRaw);
		} else {
			initializerInfo = null;
		}

		return initRec(loc, main, targetCTypeRaw, initializerInfo, onHeap, lhs);
	}

	private ExpressionResult initRec(final ILocation loc, final Dispatcher main, final CType targetCTypeRaw,
//			final InitializerResult initializerIfAnyRaw, final boolean onHeap, final LRValue lhsIfAny) {
			final InitializerInfo initInfoIfAny, final boolean onHeap, final LRValue lhsIfAny) {
//		assert initializerRaw instanceof ExpressionResult || initializerRaw instanceof InitializerResult;
		assert lhsIfAny == null
				|| lhsIfAny.getCType().getUnderlyingType().equals(targetCTypeRaw.getUnderlyingType());
		assert !onHeap || lhsIfAny != null : "we need a start address for on-heap initialization";

		final CType targetCType = targetCTypeRaw.getUnderlyingType();

		if (initInfoIfAny == null) {
			// there is no initializer -- apply default initialization
			return makeDefaultOrNondetInitialization(loc, main, lhsIfAny, targetCType, onHeap, false);
		}

		if (targetCType instanceof CPrimitive || targetCType instanceof CEnum || targetCType instanceof CPointer) {
			/*
			 * We are dealing with an initialization of a value with non-aggregate type.
			 */
			return initExpressionWithExpression(loc, main, lhsIfAny, onHeap, targetCType, initInfoIfAny);
		} else if (targetCType instanceof CStruct) {
			// unions are handled along with structs here
			return initCStruct(loc, main, lhsIfAny, (CStruct) targetCType, initInfoIfAny, onHeap);
		} else if (targetCType instanceof CArray) {
			return initCArray(loc, main, lhsIfAny, (CArray) targetCType, initInfoIfAny, onHeap,
					determineIfSophisticatedArrayInit(initInfoIfAny));
		} else {
			throw new UnsupportedOperationException("missing case for CType");
		}
	}

	private ExpressionResult initExpressionWithExpression(final ILocation loc, final Dispatcher main,
			final LRValue lhsIfAny, final boolean onHeap, final CType cType, final InitializerInfo initInfo) {
//		assert cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer;
		assert initInfo.hasExpressionResult();

		final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

		initializer.addAllExceptLrValue(initInfo.getExpressionResult());
		final RValue initializationValue = initInfo.getRValue();

		if (lhsIfAny != null) {
			// we have a lhs given, insert assignments such that the lhs is initialized
			final List<Statement> assigningStatements = makeAssignmentStatements(loc, lhsIfAny, onHeap, cType,
					initializationValue.getValue(), initInfo.getOverapprs());
			initializer.addStatements(assigningStatements);
		} else {
			initializer.setLRVal(initializationValue);
		}

		return initializer.build();
	}

	private ExpressionResult initCStruct(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CStruct cType, final InitializerInfo initInfo, final boolean onHeap) {

		if (initInfo.hasExpressionResult()) {
			// we are initializing through a struct-typed expression, not an initializer list
			return initExpressionWithExpression(loc, main, lhsIfAny, onHeap, cType, initInfo);
		}
		// we have an initializer list


		/*
		 * Builder to collect all the initialization code and possibly the result value.
		 */
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		/*
		 *  list that collects the initialization values for each field
		 */
		final ArrayList<LRValue> fieldLrValues = new ArrayList<>();

		final LRValue structBaseLhsToInitialize = obtainLhsToInitialize(loc, main, lhsIfAny, cType, onHeap,
				initialization);

		for (int i = 0; i < cType.getFieldCount(); i++) {

			if (cType instanceof CUnion && onHeap && !initInfo.hasInitInfoForIndex(i)) {
				// in on-heap case: skip assignments to fields of unions except for the one that is really written
				continue;
			}

			final LRValue currentFieldLhs;
			if (onHeap) {
				assert lhsIfAny != null && lhsIfAny instanceof HeapLValue;
				currentFieldLhs = CTranslationUtil.constructAddressForStructField(loc, main,
						(HeapLValue) structBaseLhsToInitialize, i);
			} else if (lhsIfAny != null) {
				currentFieldLhs = CTranslationUtil.constructOffHeapStructAccessLhs(loc,
						(LocalLValue) structBaseLhsToInitialize, i);
			} else {
//				currentFieldLhs = CTranslationUtil.constructOffHeapStructAccessLhs(loc,
//						(LocalLValue) structBaseLhsToInitialize, i);
				currentFieldLhs = null;
			}

			final ExpressionResult currentFieldInitialization;
			{
				final CType currentFieldUnderlyingType = cType.getFieldTypes()[i].getUnderlyingType();
//				final InitializerInfo currentFieldInitializerRawIfAny = initInfo.hasInitInfoForStructFieldNr(i) ?
//						initInfo.getInitInfoForStructFieldNr(i) : null;
				final InitializerInfo currentFieldInitializerRawIfAny = initInfo.hasInitInfoForIndex(i) ?
						initInfo.getInitInfoForIndex(i) : null;

				if (cType instanceof CUnion && !initInfo.hasInitInfoForIndex(i)) {
					assert !onHeap;
					currentFieldInitialization =
							makeDefaultOrNondetInitialization(loc, main, currentFieldLhs, currentFieldUnderlyingType,
									onHeap, true);
				} else {
					// normal case intitalize recursively with or without intitializer..
					currentFieldInitialization = initRec(loc, main, currentFieldUnderlyingType,
						currentFieldInitializerRawIfAny, onHeap, currentFieldLhs);
				}
			}
			// add the initialization code
			initialization.addAllExceptLrValue(currentFieldInitialization);

			if (currentFieldInitialization.getLrValue() != null) {
				fieldLrValues.add(currentFieldInitialization.getLrValue());
			}

			if (cType instanceof CUnion && onHeap && initInfo.hasInitInfoForIndex(i)) {
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
			final List<Expression> fieldValues = fieldLrValues.stream()
					.map(fieldLrValue -> fieldLrValue.getValue())
					.collect(Collectors.toList());
			final StructConstructor initializationValue = ExpressionFactory.constructStructConstructor(loc,
					cType.getFieldIds(),
					fieldValues.toArray(new Expression[fieldValues.size()]));

			final AssignmentStatement assignment =
					new AssignmentStatement(loc,
							new LeftHandSide[] { ((LocalLValue) structBaseLhsToInitialize).getLHS() },
							new Expression[] { initializationValue });
			addOverApprToStatementAnnots(initInfo.getOverapprs(), assignment);
			initialization.addStatement(assignment);
		}
		return initialization.build();
	}

	private ExpressionResult initCArray(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CArray cArrayType, final InitializerInfo initInfo, final boolean onHeap,
			final boolean sophisticated) {
		/*
		 * Builder where we accumulate all initialization information (Boogie code + LRValue mostly).
		 */
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		// take over code from the (converted) initializer
		if (initInfo.hasExpressionResult()) {
			initialization.addAllExceptLrValue(initInfo.getExpressionResult());
		}

		/*
		 * On-heap:
		 * Obtain the start address HeapLValue for the array intialization.
		 *
		 * Off-heap:
		 * Obtain the array that we will assign to later. (Will be the lhs, if that is non-null, or some auxiliary
		 * variable)
		 */
		final LRValue arrayLhsToInitialize = obtainLhsToInitialize(loc, main, lhsIfAny, cArrayType, onHeap,
				initialization);

		if (sophisticated) {
			// in the "sophisticated" case: make a default initialization of all array cells first
			final ExpressionResult defaultInit = makeDefaultOrNondetInitialization(loc, main, arrayLhsToInitialize, cArrayType,
					onHeap, false);
			initialization.addAllExceptLrValue(defaultInit);
		}

		/*
		 * Iterate over all array indices and assign the corresponding array cell;
		 * In the sophisticated case, only cells explicitly mentioned by the initializer are updated here.
		 * Otherwise all cells are updated
		 */
//		final List<List<Integer>> allIndicesToInitialize =
//				CrossProducts.crossProductOfSetsOfFirstNaturalNumbers(
//						CTranslationUtil.getConstantDimensionsOfArray(cArrayType, mExpressionTranslation));
//		for (final List<Integer> arrayIndex : allIndicesToInitialize) {

		if (CTranslationUtil.isToplevelVarlengthArray(cArrayType, mExpressionTranslation)) {
			throw new UnsupportedOperationException("handling varlength arrays not implemented for this case");
		}
		final int bound = CTranslationUtil.getConstantFirstDimensionOfArray(cArrayType, mExpressionTranslation);

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

			updateInitializationWithCodeForArrayCell(loc, main, cArrayType, initInfo, onHeap, initialization,
					arrayLhsToInitialize, i, arrayIndexInitInfo);
		}

		return initialization.build();
	}

	/**
	 * (maybe inline this back into its single call site)
	 *
	 * @param loc
	 * @param main
	 * @param cArrayType
	 * @param initInfo
	 * @param onHeap
	 * @param initialization
	 * @param arrayLhsToInitialize
	 * @param arrayIndex
	 * @param arrayIndexInitInfo
	 */
	private void updateInitializationWithCodeForArrayCell(final ILocation loc, final Dispatcher main,
			final CArray cArrayType, final InitializerInfo initInfo, final boolean onHeap,
			final ExpressionResultBuilder initialization, final LRValue arrayLhsToInitialize,
//			final List<Integer> arrayIndex, final InitializerInfo arrayIndexInitInfo) {
			final int arrayIndex, final InitializerInfo arrayIndexInitInfo) {

		final CType cellType = ArrayHandler.popOneDimension(cArrayType);

		if (onHeap) {
			/*
			 * initialize the array cell, if the value type is an aggregate type, this means, we have to initialize
			 * the "subcells"
			 */
			final HeapLValue arrayCellAddress = CTranslationUtil.constructAddressForArrayAtIndex(loc, main,
					(HeapLValue) arrayLhsToInitialize, arrayIndex);

			// generate and add code to initialize the array cell (and possibly its subcells)
			final ExpressionResult arrayIndexInitialization =
					initRec(loc, main, cellType, arrayIndexInitInfo, true, arrayCellAddress);
			initialization.addAllExceptLrValue(arrayIndexInitialization);


		} else {
			/*
			 * this expression result contains a value that holds the contents for the array cell at the current index
			 * (we don't give a leftHandSide to initVarRec, and use the value that is given to the ExpressionResult)
			 */

			// say we initialize multidimensional array a, build a lhs a[i] here (which still may have array type)
			final LocalLValue arrayAccessLhs = CTranslationUtil.constructArrayAccessLhs(loc,
					(LocalLValue) arrayLhsToInitialize, arrayIndex, mExpressionTranslation);

			final ExpressionResult arrayIndexInitialization =
					initRec(loc, main, cellType, arrayIndexInitInfo, false, arrayAccessLhs);
			initialization.addAllExceptLrValue(arrayIndexInitialization);


//			// assign the arrayIndexInitialization's value to the current array cell
//			initialization.addStatements(makeAssignmentStatements(loc, arrayAccessLhs, false,
//					cArrayType.getValueType(), arrayIndexInitialization.getLrValue().getValue(), initInfo.getOverapprs()));
		}
	}

	private ExpressionResult makeDefaultOrNondetInitialization(final ILocation loc, final Dispatcher main,
			final LRValue lhsIfAny, final CType cTypeRaw, final boolean onHeap, final boolean nondet) {
		assert !onHeap || lhsIfAny != null : "for on-heap initialization we need a start address";

		final CType cType = cTypeRaw.getUnderlyingType();

		final boolean sophisticated = determineIfSophisticatedDefaultInit(cType);

		/*
		 * If one of the following conditions holds, we must have an lhs for initialization.
		 * <li> we initialize something on-heap (we need a start-address to assign to
		 * <li> we initialize an array
		 */
		if (!onHeap && !(cType instanceof CArray)) {
			return makeOffHeapDefaultOrNondetInitializationForType(loc, main, cType, sophisticated,
					(LocalLValue) lhsIfAny, nondet);
		}
		// array case or on-heap case, using an lhs

		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		final LRValue lhsToInit = obtainLhsToInitialize(loc, main, lhsIfAny, cType, onHeap, initialization);

		if (onHeap) {
			final ExpressionResult defaultInit = makeOnHeapDefaultInitializationForType(loc, main,
					(HeapLValue) lhsToInit, cType, sophisticated);
			initialization.addAllExceptLrValue(defaultInit);
			assert defaultInit.getLrValue() == null : "on-heap intialization does not need a return value";
		} else {
			final ExpressionResult defaultInit = makeOffHeapDefaultOrNondetInitializationForType(loc, main, cType,
					sophisticated, (LocalLValue) lhsToInit, nondet);
			initialization.addAllExceptLrValue(defaultInit);
			if (defaultInit.getLrValue() != null) {
				assert lhsToInit == null;
				initialization.setLRVal(defaultInit.getLrValue());
			}

//			final List<Statement> lhsAssignment = makeAssignmentStatements(loc, lhsToInit, false, cType,
//					defaultInit.getLrValue().getValue(), Collections.emptyList());
//			initialization.addStatements(lhsAssignment);
		}

		return initialization.build();
	}

	private ExpressionResult makeOnHeapDefaultInitializationForType(final ILocation loc, final Dispatcher main,
			final HeapLValue baseAddress, final CType cTypeRaw, final boolean sophisticated) {
		final CType cType = cTypeRaw.getUnderlyingType();
		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {
			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();
			final List<Statement> defaultInit = makeAssignmentStatements(loc, baseAddress, true, cType,
					getDefaultValueForSimpleType(loc, cType), Collections.emptyList());
			initialization.addStatements(defaultInit);
			return initialization.build();
		} else if (cType instanceof CStruct) {
			final CStruct cStructType = (CStruct) cType;

			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

			final String[] fieldIds = cStructType.getFieldIds();

			for (int i = 0; i < fieldIds.length; i++) {
				final HeapLValue fieldPointer =
						CTranslationUtil.constructAddressForStructField(loc, main, baseAddress, i);

				final ExpressionResult fieldDefaultInit =
						makeOnHeapDefaultInitializationForType(loc, main, fieldPointer, cStructType.getFieldTypes()[i],
								sophisticated);

				initialization.addAllExceptLrValue(fieldDefaultInit);

				if (cType instanceof CUnion) {
					// only the first field in the struct that we save for a union is initialized
					break;
				}
			}
			return initialization.build();
		} else if (cType instanceof CArray) {
			if (sophisticated) {
				return makeSophisticatedOnHeapDefaultInitializationForArray(loc, main, baseAddress, (CArray) cType);
			} else {
				return makeNaiveOnHeapDefaultInitializationForArray(loc, main, baseAddress, (CArray) cType);
			}
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	/**
	 *
	 * @param loc
	 * @param main
	 * @param cTypeRaw
	 * @param sophisticated
	 * @param lhsToInitIfAny
	 * @param nondet if this is true, a nondeterministic value is used for initialization otherwise the default value
	 * @return
	 */
	private ExpressionResult makeOffHeapDefaultOrNondetInitializationForType(final ILocation loc, final Dispatcher main,
			final CType cTypeRaw, final boolean sophisticated, final LocalLValue lhsToInitIfAny, final boolean nondet) {
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {

			final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

			final LRValue initializationValue;
			if (nondet) {
				final ExpressionResult auxvar = makeUnionAuxVarExpressionResult(loc, main, cType);
				initializer.addAllExceptLrValue(auxvar);
				initializationValue = auxvar.getLrValue();
			} else {
				initializationValue = new RValue(getDefaultValueForSimpleType(loc, cType), cType);
			}


			if (lhsToInitIfAny != null) {
				// we have a lhs given, insert assignments such that the lhs is initialized
				final List<Statement> assigningStatements = makeAssignmentStatements(loc, lhsToInitIfAny, false, cType,
						initializationValue.getValue(), Collections.emptyList());
				initializer.addStatements(assigningStatements);
			} else {
				initializer.setLRVal(initializationValue);
			}
			return initializer.build();
		} else if (cType instanceof CStruct) {
			final CStruct cStructType = (CStruct) cType;

			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

			final ArrayList<LRValue> fieldLrValues = new ArrayList<>();

			for (int i = 0; i < cStructType.getFieldCount(); i++) {

				final LocalLValue fieldLhs;
				{
					if (lhsToInitIfAny == null) {
						fieldLhs = null;
					} else {
						final String fieldName = cStructType.getFieldIds()[i];
						final LeftHandSide lhs = ExpressionFactory.constructStructAccessLhs(loc, lhsToInitIfAny.getLHS(),
								fieldName);
						fieldLhs = new LocalLValue(lhs, cStructType.getFieldTypes()[i]);
					}
				}


				final ExpressionResult fieldDefaultInit;
				if (cType instanceof CUnion && i != 0) {
					/*
					 * In case of a union, all fields not mentioned in the initializer are havocced, thus their default
					 * initialization is a fresh auxiliary variable.
					 * However there is one exception: the first field is default-inititalized.
					 */
					fieldDefaultInit =
						makeOffHeapDefaultOrNondetInitializationForType(loc, main, cStructType.getFieldTypes()[i],
								sophisticated, fieldLhs, true);
				} else {
					fieldDefaultInit =
						makeOffHeapDefaultOrNondetInitializationForType(loc, main, cStructType.getFieldTypes()[i],
								sophisticated, fieldLhs, nondet);
				}

				initialization.addAllExceptLrValue(fieldDefaultInit);
				fieldLrValues.add(fieldDefaultInit.getLrValue());
			}

			if (lhsToInitIfAny == null) {
				final List<Expression> fieldValues = fieldLrValues.stream()
						.map(LRValue::getValue)
						.collect(Collectors.toList());
				final StructConstructor initializationValue = ExpressionFactory.constructStructConstructor(loc,
						cStructType.getFieldIds(),
						fieldValues.toArray(new Expression[fieldValues.size()]));
				initialization.setLRVal(new RValue(initializationValue, cType));
			}

			return initialization.build();
		} else if (cType instanceof CArray) {
			if (sophisticated) {
				return makeSophisticatedOffHeapDefaultInitializationForArray(loc, main, (CArray) cType, nondet);
			} else {
				return makeNaiveOffHeapDefaultOrNondetInitForArray(loc, main, (CArray) cType, lhsToInitIfAny, nondet);
			}
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	protected ExpressionResult makeUnionAuxVarExpressionResult(final ILocation loc, final Dispatcher main,
			final CType fieldType) {
		final AuxVarHelper auxVar = CTranslationUtil.makeAuxVarDeclaration(loc, main, fieldType,
				SFO.AUXVAR.UNION);

		final ExpressionResult x = new ExpressionResultBuilder()
				.setLRVal(new RValue(auxVar.getExp(), fieldType))
				.addDeclaration(auxVar.getVarDec())
				.putAuxVar(auxVar.getVarDec(), loc)
				.addOverapprox(new Overapprox("initialize union -- havoccing a field without explictit "
						+ "initializer", loc))
				.build();
		return x;
	}

	private ExpressionResult makeNaiveOnHeapDefaultInitializationForArray(final ILocation loc, final Dispatcher main,
			final HeapLValue baseAddress, final CArray cArrayType) {
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		final List<List<Integer>> allIndicesToInitialize =
				CrossProducts.crossProductOfSetsOfFirstNaturalNumbers(
						CTranslationUtil.getConstantDimensionsOfArray(cArrayType, mExpressionTranslation));
		for (final List<Integer> arrayIndex : allIndicesToInitialize) {
			final HeapLValue arrayAccessLhs = CTranslationUtil.constructAddressForArrayAtIndex(loc, main, baseAddress,
					arrayIndex);

			final ExpressionResult arrayIndexInitialization =
					makeOnHeapDefaultInitializationForType(loc, main, arrayAccessLhs, cArrayType.getValueType(), false);
			initialization.addAllExceptLrValue(arrayIndexInitialization);
		}
		return initialization.build();
	}

	private ExpressionResult makeSophisticatedOnHeapDefaultInitializationForArray(final ILocation loc,
			final Dispatcher main, final HeapLValue baseAddress, final CArray cType) {
		throw new UnsupportedOperationException("TODO"); //TODO
	}

	private ExpressionResult makeNaiveOffHeapDefaultOrNondetInitForArray(final ILocation loc, final Dispatcher main,
				final CArray cArrayType, final LocalLValue lhsToInit, final boolean nondet) {
			assert lhsToInit != null;

			final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

			final LocalLValue arrayLhsToInitialize = lhsToInit;

			final List<List<Integer>> allIndicesToInitialize =
					CrossProducts.crossProductOfSetsOfFirstNaturalNumbers(
							CTranslationUtil.getConstantDimensionsOfArray(cArrayType, mExpressionTranslation));
			for (final List<Integer> arrayIndex : allIndicesToInitialize) {

				final LocalLValue arrayAccessLhs = CTranslationUtil.constructArrayAccessLhs(loc,
						arrayLhsToInitialize, arrayIndex, mExpressionTranslation);

				final ExpressionResult arrayIndexInitialization =
						makeOffHeapDefaultOrNondetInitializationForType(loc, main, cArrayType.getValueType(), false,
								arrayAccessLhs, nondet);
				initialization.addAllExceptLrValue(arrayIndexInitialization);


//				// assign the arrayIndexInitialization's value to the current array cell
//				initialization.addStatements(makeAssignmentStatements(loc, arrayAccessLhs, false,
//						cArrayType.getValueType(), arrayIndexInitialization.getLrValue().getValue(),
//						Collections.emptyList()));
			}

			return initialization.build();
		}

	private ExpressionResult makeSophisticatedOffHeapDefaultInitializationForArray(final ILocation loc,
			final Dispatcher main, final CArray cArrayType, final boolean nondet) {
		throw new UnsupportedOperationException("TODO"); //TODO
	}

	/**
	 * Side effect notice: This method may update the given initialization with declarations for an auxiliary variable
	 *  and possibly set the LrValue.
	 *
	 * @param loc
	 * @param main
	 * @param lhsIfAny
	 * @param cType
	 * @param onHeap
	 * @param initialization
	 * @return
	 */
	private LRValue obtainLhsToInitialize(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CType cType, final boolean onHeap, final ExpressionResultBuilder initialization) {
		final LRValue arrayLhsToInitialize;
		if (onHeap) {
			assert lhsIfAny != null && lhsIfAny instanceof HeapLValue;
			arrayLhsToInitialize = lhsIfAny;
		} else {
			arrayLhsToInitialize = obtainLocalLValueToInitialize(loc, main, (LocalLValue) lhsIfAny, cType,
					initialization);
		}
		return arrayLhsToInitialize;
	}

	/**
	 *
	 * @param loc
	 * @param main
	 * @param cType
	 * @param initialization side effects on this parameter: is updated with the necessary declaration and the returned
	 * 	LocalLValue is set as LrValue
	 * @return
	 */
	private LocalLValue obtainLocalLValueToInitialize(final ILocation loc, final Dispatcher main,
			final LocalLValue lhsIfAny, final CType cType, final ExpressionResultBuilder initialization) {
		final LocalLValue arrayLhsToInitialize;
		if (lhsIfAny != null) {
			arrayLhsToInitialize = lhsIfAny;
		} else {
			// we need an auxiliary variable for the array to be the value of the ExpressionResult we return.
			arrayLhsToInitialize = obtainAuxVarLocalLValue(loc, main, cType, initialization);
		}
		return arrayLhsToInitialize;
	}

	/**
	 *
	 * @param loc
	 * @param main
	 * @param cType
	 * @param initialization side effects on this parameter: is updated with the necessary declaration and the returned
	 * 	LocalLValue is set as LrValue
	 * @return
	 */
	private LocalLValue obtainAuxVarLocalLValue(final ILocation loc, final Dispatcher main, final CType cType,
			final ExpressionResultBuilder initialization) {
		final LocalLValue arrayLhsToInitialize;
		final AuxVarHelper auxVar = CTranslationUtil.makeAuxVarDeclaration(loc, main, cType);

		arrayLhsToInitialize = new LocalLValue(auxVar.getLhs(), cType);

		initialization.addDeclaration(auxVar.getVarDec());
		initialization.putAuxVar(auxVar.getVarDec(), loc);
		initialization.setLRVal(arrayLhsToInitialize);
		return arrayLhsToInitialize;
	}

	/**
	 * Returns a call to the special array initialization procedure. ("off-heap" case)
	 * This procedure returns an array with the given signature where all cells within the given ranges have been
	 * initialized to the default value for the given value type.
	 *
	 * (Whether the initialization procedure will initialize cells beyond these ranges may vary between different
	 * implementations of that procedure.)
	 *
	 * @param lhs the variable that the return value of the initialization procedure should be assigned to
	 * @param dimensions the dimensions of the C array to initialize, this specifies both the index types
	 *   (should be integer) and the ranges for each array dimension.
	 * @param valueType the type that the entries in the innermost arrays have
	 * @return
	 */
	private Statement getInitializerArrayCall(final LocalLValue lhs, final CArray arrayType) {
		mDeclareArrayInitializationFunction = true;

		// TODO Auto-generated method stub
		return null;
	}



	/**
	 * Returns a call to the special array initialization procedure. ("on-heap" case)
	 * The initialization procedure takes as arguments a memory address and signature and range information for an
	 * array.
	 * The procedure ensures that after it has been called all the memory cells belonging to the given array and ranges
	 * have been initialized to the default value.
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


	public List<Declaration> declareInitializationInfrastructure(final Dispatcher main, final ILocation loc) {
		return Collections.emptyList();
	}


	/**
	 * Construct assignment statements that make sure that "lhs" gets the value "initializationValue".
	 *
	 * @param loc
	 * @param lhs
	 * @param onHeap
	 * @param cType
	 * @param initializationValue
	 * @param overAppr
	 * @return
	 */
	private List<Statement> makeAssignmentStatements(final ILocation loc, final LRValue lhs,
			final boolean onHeap, final CType cType, final Expression initializationValue,
			final Collection<Overapprox> overAppr) {
		assert lhs != null;

		List<Statement> assigningStatements;
		if (onHeap) {
			assigningStatements = mMemoryHandler.getWriteCall(loc, (HeapLValue) lhs, initializationValue,
					cType);
		} else {
			//!onHeap
			final AssignmentStatement assignment =
					new AssignmentStatement(loc,
							new LeftHandSide[] { ((LocalLValue) lhs).getLHS() },
							new Expression[] { initializationValue });
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
				return mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive,
						BigInteger.ZERO);
			case FLOATTYPE:
				return mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive,
						BigDecimal.ZERO);
			case VOID:
				throw new AssertionError("cannot initialize something that has type void");
			default:
				throw new AssertionError("unknown category of type");
			}
		} else if (cType instanceof CEnum) {
			return mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
					BigInteger.ZERO);
		} else if (cType instanceof CPointer) {
			return mExpressionTranslation.constructNullPointer(loc);
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}


	/**
	 * Determines which kind of initialization code we want to generate. There are two variants
	 * <li> "naive": We generate a sequence of assignments that initialize each field of the aggregate type object.
	 * <li> "sophisticated": We first initialize the whole object to default values and then insert assignments that
	 *   initialize the fields that are explicitly mentioned by the initializer.
	 *   The first step may be performed in different ways, for instance by while loops, or by using special SMT
	 *   default arrays.
	 * <p>
	 * Some criteria for when to choose which:
	 * <li> when "most" of the initialized values are initialized explicitly, we choose "naive", for some threshold
	 * <li> variable length arrays need "sophisticated"
	 *
	 * @param initializerIfAny
	 * @return true iff sophisticated initialization should be applied
	 */
	private boolean determineIfSophisticatedArrayInit(final InitializerInfo initInfoIfAny) {
		// TODO implement some heuristics
		return false;
	}

	/**
	 * For the given type. Determine if we want to make a sophisticated or a naive initialization.
	 * See also {@link determineIfSophisticatedArrayInit}.
	 *
	 * @param targetCType
	 * @return
	 */
	private boolean determineIfSophisticatedDefaultInit(final CType targetCType) {
		// TODO implement some heuristics
		return false;
	}


	/**
	 * Represents all information that is needed to initialize a given target expression with a given initializer.
	 * Is generated from an InitializerResult together with the target expression's CType.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	static class InitializerInfo {

		private final ExpressionResult mExpressionResult;
		private final Collection<Overapprox> mOverApprs;


//		/*
//		 * Initialization information for when the target CType is a CArray
//		 */
//		private final Map<List<Integer>, InitializerInfo> mArrayIndexToInitInfo;
//
//		/*
//		 * Initialization information for when the target CType is a CStruct.
//		 * Note that his list may have "gaps" (i.e. null entries) because of designated initializers.
//		 */
//		private final List<InitializerInfo> mStructFieldInitInfos;

//		private final List<InitializerInfo> mElementInitInfos;
		private final Map<Integer, InitializerInfo> mElementInitInfos;

		/**
		 * Used only during building the InitializerInfo. An inner initialization may leave over values for an outer
		 * initialization.
		 */
		private final List<InitializerResult> mUnusedListEntries;

		private InitializerInfo(final ExpressionResult expressionResult, final List<InitializerResult> rest) {
			assert expressionResult.getLrValue() == null || expressionResult.getLrValue() instanceof RValue :
				"switch to RValue first!";
			mExpressionResult = expressionResult;
			mOverApprs = expressionResult.getOverapprs();
			mElementInitInfos = null;
			mUnusedListEntries = rest;
//			mArrayIndexToInitInfo = null;
//			mStructFieldInitInfos = null;
		}

		public InitializerInfo(final Map<Integer, InitializerInfo> indexInitInfos,
				final List<InitializerResult> unused) {
			mExpressionResult = null;
			mOverApprs = null;
			mElementInitInfos = indexInitInfos;
			mUnusedListEntries = unused;
		}

//		private InitializerInfo(final Map<List<Integer>, InitializerInfo> arrayIndexToInitInfo) {
//			mExpressionResult = null;
//			mOverApprs = null;
//			mArrayIndexToInitInfo = arrayIndexToInitInfo;
//			mStructFieldInitInfos = null;
//		}

//		private InitializerInfo(final List<InitializerInfo> structFieldInitInfos) {
//			mExpressionResult = null;
//			mOverApprs = null;
//			mArrayIndexToInitInfo = null;
//			mStructFieldInitInfos = structFieldInitInfos;
//		}

		/**
		 * Converts a given InitializerResult to an InitializerInfo with respect to a given target CType.
		 *
		 * The target CType is the CType of the C object that will be initialized with the initializer that the
		 * InitializerResult has been generated from.
		 * Conceptually, the target CType is important because conversions may need to be applied according to it
		 * (e.g. a "0" may become the NULL pointer), and designated initializers may need to be reordered according to
		 * the field names of a target CStruct type.
		 *
		 * @param initializerResult
		 * @param targetCType
		 */
		public static InitializerInfo constructInitializerInfo(final ILocation loc, final Dispatcher main,
//				final List<InitializerResult> initializerResult, final CType targetCTypeRaw) {
				final InitializerResult initializerResult, final CType targetCTypeRaw) {
			final CType targetCType = targetCTypeRaw.getUnderlyingType();

			if (!initializerResult.isInitializerList()) {
				// we are initializing through a struct-type expression (as in "struct s s1 = s2;")

				final ExpressionResult converted = convertInitResultWithExpressionResult(loc, main, targetCType,
						initializerResult);
				return new InitializerInfo(converted, Collections.emptyList());
			}

			if (targetCType instanceof CArray || targetCType instanceof CStruct) {
//				// aggregate or union type
				return constructIndexToInitInfo(loc, main, initializerResult.getList(), targetCType);
//			} else if (targetCType instanceof CStruct) {
//				// target type is a struct or a union type
//				return constructArrayIndexToInitInfo(loc, main, initializerResult.getList(), targetCType);
			} else {
				// target type is simple

				// do the necessary conversions
				final Deque<InitializerResult> ad = new ArrayDeque<>(initializerResult.getList());
				final InitializerResult first = ad.pollFirst();

				final ExpressionResult expressionResultSwitched =
						convertInitResultWithExpressionResult(loc, main, targetCType, first);

				return new InitializerInfo(expressionResultSwitched, new ArrayList<>(ad));


			}
		}

		protected static ExpressionResult convertInitResultWithExpressionResult(final ILocation loc,
				final Dispatcher main, final CType targetCType, final InitializerResult first) {
			final ExpressionResult expressionResultSwitched = first.getRootExpressionResult()
					.switchToRValueIfNecessary(main, loc);
			expressionResultSwitched.rexBoolToIntIfNecessary(loc, main.mCHandler.getExpressionTranslation());
			// 2017-11-19 Matthias: introduced workaround to omit conversion
			if ((expressionResultSwitched.getLrValue().getCType() instanceof CArray)) {
				// omit conversion
			} else {
				main.mCHandler.convert(loc, expressionResultSwitched, targetCType);
			}
			return expressionResultSwitched;
		}

		private static InitializerInfo constructIndexToInitInfo(final ILocation loc, final Dispatcher main,
				final List<InitializerResult> initializerResults, final CType targetCType) {
			assert targetCType instanceof CArray || targetCType instanceof CStruct;

			final Map<Integer, InitializerInfo> indexInitInfos = new HashMap<>();

			Deque<InitializerResult> rest = new ArrayDeque<>(initializerResults);

			final int bound;
			CType cellType = null;
			{
				if (targetCType instanceof CArray) {
					cellType = ArrayHandler.popOneDimension((CArray) targetCType);
					bound = CTranslationUtil.getConstantFirstDimensionOfArray((CArray) targetCType,
							main.mCHandler.getExpressionTranslation());
					if (CTranslationUtil.isToplevelVarlengthArray((CArray) targetCType,
							main.mCHandler.getExpressionTranslation())) {
						throw new UnsupportedOperationException("varlenght not yet supported here");
					}
				} else {
					// targetCType instanceof CStruct
					bound = ((CStruct) targetCType).getFieldCount();
				}
			}



			/*
			 * The currentCellIndex stands for the "current object" from the standard text.
			 * Designators may modify that index otherwise it just counts up.
			 */
			int currentCellIndex = -1;
			while (currentCellIndex < bound && !rest.isEmpty()) {
//			for (int currentCellIndex = 0; currentCellIndex < bound; currentCellIndex++) {
				if (rest.peekFirst().hasRootDesignator()) {
					assert targetCType instanceof CStruct : "array designators not yet supported and should not (yet)"
							+ " show up here";
					currentCellIndex = CTranslationUtil.findIndexOfStructField((CStruct) targetCType,
							rest.peekFirst().getRootDesignator());
				} else {
					currentCellIndex++;
				}

//				if (rest.isEmpty()) {
//					// no more values in the current initializer list
//					break;
//				}

				if (targetCType instanceof CStruct) {
					cellType = ((CStruct) targetCType).getFieldTypes()[currentCellIndex];
				}



				/*
				 * C11 6.7.9.13
				 *  The initializer for a structure or union object that has automatic storage duration shall be
				 *  either an initializer list as described below, or a single expression that has compatible
				 *  structure or union type. In the latter case, the initial value of the object, including
				 *  unnamed members, is that of the expression.
				 */
				if (rest.peekFirst().isInitializerList() ||
						// TODO: make a more general compatibility check, for example for array and pointer
						TypeHandler.isCompatibleStructOrUnionType(cellType,
								rest.peekFirst().getRootExpressionResult().getLrValue().getCType())) {
					/*
					 * case "{", i.e. one more brace opens
					 * Then the cell is initialized with the list belonging to that brace (until the matching brace).
					 * No residue is taken over if too many elements are left.
					 *
					 * other case: first list entry has a compatible struct or union type
					 */

					final InitializerResult first = rest.pollFirst();
//					final InitializerInfo cellInitInfo = constructInitializerInfo(loc, main, first.getList(), cellType);
					final InitializerInfo cellInitInfo = constructInitializerInfo(loc, main, first, cellType);

					indexInitInfos.put(currentCellIndex, cellInitInfo);
				} else {
					/*
					 * Case where the list starts with a value (or identifier, just not with a brace).
					 * Then the current list is handed down to the cell, and if anything is left after processing that
					 * cell we use it for the next cell.
					 */
					final InitializerResultBuilder restInitResultBuilder = new InitializerResultBuilder();
					rest.forEach(restInitResultBuilder::addChild);
					final InitializerInfo cellInitInfo = constructInitializerInfo(loc, main,
							restInitResultBuilder.build(),
//							new ArrayList<>(rest),
							cellType);
					indexInitInfos.put(currentCellIndex, cellInitInfo);
					rest = new ArrayDeque<>(cellInitInfo.getUnusedListEntries());
				}
			}

			return new InitializerInfo(indexInitInfos, new ArrayList<>(rest));
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

//		public boolean hasInitInfoForStructFieldNr(final int i) {
//			return mStructFieldInitInfos.size() > i && mStructFieldInitInfos.get(i) != null;
//		}
//
//		public InitializerInfo getInitInfoForStructFieldNr(final int i) {
//			if (!hasInitInfoForStructFieldNr(i)) {
//				throw new IllegalArgumentException("check hasInitInfoForStructFieldNr before calling this method");
//			}
//			return mStructFieldInitInfos.get(i);
//		}

//		public Collection<List<Integer>> getArrayIndicesWithInitInfo() {
//			return mArrayIndexToInitInfo.keySet();
//		}
//
//		public boolean hasInitInfoForArrayIndex(final List<Integer> arrayIndex) {
//			return getArrayIndicesWithInitInfo().contains(arrayIndex);
//		}
//
//		public InitializerInfo getInitInfoForArrayIndex(final List<Integer> arrayIndex) {
//			assert mArrayIndexToInitInfo.get(arrayIndex) != null;
//			return mArrayIndexToInitInfo.get(arrayIndex);
//		}

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

		@Override
		public String toString() {
			if (mExpressionResult != null) {
				return mExpressionResult.toString();
			}
			if (mElementInitInfos != null) {
				return mElementInitInfos.toString();
			}
//			if (mArrayIndexToInitInfo != null) {
//				return mArrayIndexToInitInfo.toString();
//			}
//			if (mStructFieldInitInfos != null) {
//				return mStructFieldInitInfos.toString();
//			}
			return "?";
		}
	}
}
