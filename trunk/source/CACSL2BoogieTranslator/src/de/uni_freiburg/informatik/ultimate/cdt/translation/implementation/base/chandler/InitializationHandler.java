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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResult;
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
 * One relevant entry in C11 draft, 6.7.9.10:
 * If an object that has automatic storage duration is not initialized explicitly, its value is
 * indeterminate. If an object that has static or thread storage duration is not initialized
 * explicitly, then:
 *  <li> if it has pointer type, it is initialized to a null pointer;
 *  <li> if it has arithmetic type, it is initialized to (positive or unsigned) zero;
 *  <li> if it is an aggregate, every member is initialized (recursively) according to these rules,
 *    and any padding is initialized to zero bits;
 *  <li> if it is a union, the first named member is initialized (recursively) according to these
 *    rules, and any padding is initialized to zero bits;
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
	public ExpressionResult initVarNew(final ILocation loc, final Dispatcher main, final LeftHandSide lhsRaw,
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

		return initVarRec(loc, main, targetCTypeRaw, initializerRaw, onHeap, lhs);
	}

	private ExpressionResult initVarRec(final ILocation loc, final Dispatcher main, final CType targetCTypeRaw,
			final InitializerResult initializerIfAnyRaw, final boolean onHeap, final LRValue lhsIfAny) {
//		assert initializerRaw instanceof ExpressionResult || initializerRaw instanceof InitializerResult;
		assert lhsIfAny == null || lhsIfAny.getCType().equals(targetCTypeRaw.getUnderlyingType());

		final CType targetCType = targetCTypeRaw.getUnderlyingType();

		if (initializerIfAnyRaw == null) {
			final boolean sophisticated = determineSophisticatedDefaultInit(targetCType);
			if (lhsIfAny != null) {
				return makeDefaultInitAndAssignToLhs(loc, lhsIfAny, targetCType, onHeap, sophisticated);
			} else {
				return getDefaultInitializationForType(loc, targetCType, sophisticated);
			}
		}


		assert initializerIfAnyRaw instanceof InitializerResult;

		InitializerResult initializerConverted = null;
		if (initializerIfAnyRaw != null ) {
			//				final ExpressionResult initializerRawSwitched =
			//						((ExpressionResult) initializerRaw).switchToRValueIfNecessary(main, mMemoryHandler,
			//								mStructHandler, loc);
			//				initializerRawSwitched.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			final InitializerResult initializerBoolToInt =
					initializerIfAnyRaw.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

			/*
			 * Conversions need to be applied here (like for a normal assignment), because the rhs of an
			 * initialization may not be of the right type.
			 * Simplest example: "int * i = 0", here the "0" must be converted to the null pointer.
			 */
			//				main.mCHandler.convert(loc, initializerRawSwitched, cType);
			initializerConverted =
					initializerBoolToInt.convert(loc, main, targetCType);

			assert initializerConverted.getTreeNodeIds().isEmpty();
		}

		if (targetCType instanceof CPrimitive || targetCType instanceof CEnum || targetCType instanceof CPointer) {
			/*
			 * We are dealing with an initialization of a value with non-aggregate type.
			 */
			return initExpressionWithSimpleType(loc, main, lhsIfAny, onHeap, targetCType, initializerConverted);
		} else if (targetCType instanceof CStruct && onHeap) {
			return initCStructOnHeap(loc, main, lhsIfAny, (CStruct) targetCType, initializerConverted);
		} else if (targetCType instanceof CStruct && !onHeap) {
			return initCStructOffHeap(loc, main, lhsIfAny, (CStruct) targetCType, initializerConverted);
		} else if (targetCType instanceof CArray) {
			return initCArray(loc, main, lhsIfAny, (CArray) targetCType, initializerConverted, onHeap);
//		} else if (targetCType instanceof CArray && onHeap) {
//			return initCArrayOnHeap(loc, main, (HeapLValue) lhs, (CArray) targetCType,
////					initializerRaw == null ? null : ((InitializerResult) initializerRaw).list);
////					initializerRaw == null ? null : initializerConverted.getTopLevelChildren());
//					initializerConverted);
//		} else if (targetCType instanceof CArray && !onHeap) {
//			return initCArrayOffHeap(loc, main, (LocalLValue) lhs, (CArray) targetCType,
////					initializerRaw == null ? null : initializerConverted.getTopLevelChildren());
//					initializerConverted);
		} else {
			throw new UnsupportedOperationException("missing case for CType");
		}
	}


	private boolean determineSophisticatedDefaultInit(final CType targetCType) {
		// TODO Auto-generated method stub
		return false;
	}

	private ExpressionResult initExpressionWithSimpleType(final ILocation loc, final Dispatcher main,
			final LRValue lhsIfAny, final boolean onHeap, final CType cType,
//			final ExpressionResultBuilder initializerIfAny) {
			final InitializerResult initializerConverted) {
		assert cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer;


		final ExpressionResultBuilder initializer;
		final Expression initializationValue;

		if (initializerConverted != null) {
			/*
			 * There is initialization code in the C program.
			 * Conversions have already been applied by the calling method, so we can just use the value in
			 * initializerIfAny.
			 */

			// prepare builder --> transfer already accumulated Boogie code
			initializer = new ExpressionResultBuilder();
			initializer.addStatements(initializerConverted.getExpressionResult().getStatements());
			initializer.addDeclarations(initializerConverted.getExpressionResult().getDeclarations());
			initializer.addOverapprox(initializerConverted.getExpressionResult().getOverapprs());
			initializer.putAuxVars(initializerConverted.getExpressionResult().getAuxVars());
//			initializer.setLRVal(initializerConverted.getExpressionResult().getLrValue());
			assert initializerConverted.getExpressionResult().otherUnionFields == null || initializerConverted.getExpressionResult().otherUnionFields.isEmpty();

			initializationValue = initializerConverted.getExpressionResult().getLrValue().getValue();
//			initializer = initializerIfAny;
		} else {
			// there is no initialization code in the C program --> initialize to defaults
			initializationValue = getDefaultValueForSimpleType(loc, cType);
			initializer = new ExpressionResultBuilder();
//			initializer.setLRVal(new RValue(initializationValue, cType));
		}

		if (lhsIfAny != null) {
			// we have a lhs given, insert assignments such that the lhs is initialized

			// TODO: the role of the overAppr is a bit unclear -- think about it..
			final List<Overapprox> overAppr = initializer.mOverappr;

			List<Statement> assigningStatements;
			assigningStatements = makeAssignmentStatements(loc, lhsIfAny, onHeap, cType, initializationValue,
					overAppr);
			initializer.addStatements(assigningStatements);
		} else {
			initializer.setLRVal(new RValue(initializationValue, cType));
		}

		return initializer.build();
	}

	private ExpressionResult initCStructOffHeap(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CStruct cType, final InitializerResult initializerRaw) {
		/*
		 *  list that collects the initialization values for each field
		 */
		final ArrayList<Expression> fieldValues = new ArrayList<>();
		/*
		 *  builder to collect any auxiliary declarations, statements etc. that may occur during obtaining the field
		 *  values
		 */
		final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

		for (int i = 0; i < cType.getFieldCount(); i++) {
			final ExpressionResult currentFieldInitializer;
			{
				final CType currentFieldUnderlyingType = cType.getFieldTypes()[i].getUnderlyingType();
				final InitializerResult	currentFieldInitializerRawIfAny = null; //TODO

				currentFieldInitializer =
						initVarRec(loc, main, currentFieldUnderlyingType, currentFieldInitializerRawIfAny, false, null);
			}
			initializer.addAllExceptLrValue(currentFieldInitializer);
			fieldValues.add(currentFieldInitializer.getLrValue().getValue());
		}

		final StructConstructor initializationValue = new StructConstructor(loc,
				cType.getFieldIds(),
				fieldValues.toArray(new Expression[fieldValues.size()]));


		if (lhsIfAny != null) {
			final AssignmentStatement assignment =
					new AssignmentStatement(loc,
							new LeftHandSide[] { ((LocalLValue) lhsIfAny).getLHS() },
							new Expression[] { initializationValue });
			addOverApprToStatementAnnots(initializer.mOverappr, assignment);
			initializer.addStatement(assignment);
		} else {
			initializer.setLRVal(new RValue(initializationValue, cType));
		}

		return initializer.build();
	}

	private ExpressionResult initCStructOnHeap(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CStruct cType, final InitializerResult initializerRaw) {


		final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

		final String[] fieldIds = cType.getFieldIds();
		final CType[] fieldTypes = cType.getFieldTypes();

		// the new Arrays for the StructConstructor
		final ArrayList<String> fieldIdentifiers = new ArrayList<>();
		final ArrayList<Expression> fieldValues = new ArrayList<>();

		for (int i = 0; i < cType.getFieldCount(); i++) {
			fieldIdentifiers.add(fieldIds[i]);

			final CType currentFieldsUnderlyingType = fieldTypes[i].getUnderlyingType();

			final ExpressionResult fieldContents = null;

		}

		return initializer.build();

		// nolhs
//		final CStruct structType = (CStruct) lCType;
//
//		final ExpressionResult scRex =
//				makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
//
//		stmt.addAll(scRex.stmt);
//		decl.addAll(scRex.decl);
//		overappr.addAll(scRex.overappr);
//		auxVars.putAll(scRex.auxVars);
//		rhs = null;
//		lrVal = new RValue(rhs, lCType);

		// lhs
//		final CStruct structType = (CStruct) lCType;
//
//		if (onHeap) {
//			assert var != null;
//			final ExpressionResult heapWrites = initStructOnHeapFromRERL(main, loc, ((HeapLValue) var).getAddress(),
//					(ExpressionListRecResult) initializer, structType);
//
//			stmt.addAll(heapWrites.stmt);
//			decl.addAll(heapWrites.decl);
//			overappr.addAll(heapWrites.overappr);
//			auxVars.putAll(heapWrites.auxVars);
//		} else {
// ...
//		}

	}

//	private ExpressionResult initCArrayOnHeap(final ILocation loc, final Dispatcher main, final HeapLValue lhsIfAny,
//			final CArray cType, final InitializerResult initializerIfAny) {
//
//		return null;
//	}

	private ExpressionResult initCArrayOnHeapNaive(final ILocation loc, final Dispatcher main,
			final HeapLValue lhsIfAny, final CArray cArrayType, final InitializerResult initializerConvertedIfAny) {
		return null;
	}

	private ExpressionResult initCArrayOnHeapSophisticated(final ILocation loc, final Dispatcher main,
			final HeapLValue lhsIfAny, final CArray cArrayType, final InitializerResult initializerConverted) {

		return null;
	}


	private ExpressionResult initCArrayOffHeapNaive(final ILocation loc, final Dispatcher main,
			final LocalLValue lhsIfAny, final CArray cArrayType, final InitializerResult initializerConverted) {
		/*
		 * Builder where we accumulate all initialization information (Boogie code + LRValue mostly).
		 */
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		/*
		 * We may create new Boogie statements in this method. Those need to get the overapproximation flags from the
		 * initializer if any are present.
		 * The variable overAppr holds them.
		 */
		final Collection<Overapprox> overAppr = initializerConverted.getExpressionResult().getOverapprs();
		// take over code from the (converted) initializer
		initialization.addAllExceptLrValue(initializerConverted.getExpressionResult());

		/*
		 * Obtain the array that we will assign to later. (Will be the lhs, if that is non-null, or some auxiliary
		 * variable)
		 */
		final LocalLValue arrayLhsToInitialize = obtainArrayLhsToInitialize(loc, main, lhsIfAny, cArrayType,
				initialization);

		/*
		 * Iterate over all array indices and assign the corresponding array cell;
		 */
		final List<List<Integer>> allIndicesToInitialize =
				CrossProducts.crossProductOfSetsOfFirstNaturalNumbers(getConstantDimensions(cArrayType));
		for (final List<Integer> arrayIndex : allIndicesToInitialize) {
			final Expression initializationValue;
			if (initializerConverted.hasTreeNode(arrayIndex)) {
				// the initializer has a value for the current array cell
				initializationValue = initializerConverted.getTreeNode(arrayIndex).getLrValue().getValue();
			} else {
				// the initializer has no value for the current array cell --> assign the default value
				final ExpressionResult defaultInit = getNaiveDefaultInitializationForType(loc, cArrayType.getValueType());
				initialization.addAllExceptLrValue(defaultInit);
				initializationValue = defaultInit.getLrValue().getValue();
			}

			final LocalLValue arrayAccessLhs = CTranslationUtil.constructArrayAccessLhs(loc, arrayLhsToInitialize,
					arrayIndex, mExpressionTranslation);
			initialization.addStatements(makeAssignmentStatements(loc, arrayAccessLhs, false,
					cArrayType.getValueType(), initializationValue, overAppr));
		}

		return initialization.build();
	}

	private ExpressionResult initCArrayOffHeapSophisticated(final ILocation loc, final Dispatcher main,
			final LocalLValue lhsIfAny, final CArray cArrayType, final InitializerResult initializerConverted) {
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		/*
		 * We may create new Boogie statements in this method. Those need to get the overapproximation flags from the
		 * initializer if any are present.
		 * The variable overAppr holds them.
		 */
		final Collection<Overapprox> overAppr = initializerConverted.getExpressionResult().getOverapprs();
		// take over code from the (converted) initializer
		initialization.addAllExceptLrValue(initializerConverted.getExpressionResult());

		/*
		 * Obtain the array that we will assign to later. (Will be the lhs, if that is non-null, or some auxiliary
		 * variable)
		 */
		final LocalLValue arrayLhsToInitialize = obtainArrayLhsToInitialize(loc, main, lhsIfAny, cArrayType,
				initialization);

		// first, make a (sophisticated) default initialization
		final ExpressionResult defaultInit =
				makeDefaultInitAndAssignToLhs(loc, arrayLhsToInitialize, cArrayType, false, true);
		initialization.addAllExceptLrValue(defaultInit);

		// second, (re)assign all values that the initializer explicitly mentions
		for (final List<Integer> arrayIndex : initializerConverted.getTreeNodeIds()) {
			final Expression initializationValue = initializerConverted.getTreeNode(arrayIndex).getLrValue().getValue();

			final LocalLValue arrayAccessLhs = CTranslationUtil.constructArrayAccessLhs(loc, arrayLhsToInitialize,
					arrayIndex, mExpressionTranslation);

			initialization.addStatements(makeAssignmentStatements(loc, arrayAccessLhs, false,
					cArrayType.getValueType(), initializationValue, overAppr));
		}

		return initialization.build();
	}

	protected LocalLValue obtainArrayLhsToInitialize(final ILocation loc, final Dispatcher main,
			final LocalLValue lhsIfAny, final CArray cArrayType, final ExpressionResultBuilder initialization) {
		final LocalLValue arrayLhsToInitialize;
		if (lhsIfAny != null) {
			arrayLhsToInitialize = lhsIfAny;
		} else {
			// we need an auxiliary variable for the array to be the value of the ExpressionResult we return.
			final AuxVarHelper auxVar = CTranslationUtil.makeAuxVarDeclaration(loc, main, SFO.AUXVAR.ARRAYINIT,
					cArrayType);

			arrayLhsToInitialize = new LocalLValue(auxVar.getLhs(), cArrayType);

			initialization.addDeclaration(auxVar.getVarDec());
			initialization.setLRVal(arrayLhsToInitialize);
		}
		return arrayLhsToInitialize;
	}

	protected ExpressionResult makeDefaultInitAndAssignToLhs(final ILocation loc, final LRValue lhsIfAny,
			final CType cType, final boolean onHeap, final boolean sophisticated) {
		final ExpressionResultBuilder initialization = new ExpressionResultBuilder();

		final ExpressionResult defaultInit = getDefaultInitializationForType(loc, cType, sophisticated);
		initialization.addAllExceptLrValue(defaultInit);

		final List<Statement> lhsAssignment = makeAssignmentStatements(loc, lhsIfAny, onHeap, cType,
				defaultInit.getLrValue().getValue(), Collections.emptyList());
		initialization.addStatements(lhsAssignment);

		return initialization.build();
	}

	private ExpressionResult getDefaultInitializationForType(final ILocation loc, final CType cType,
			final boolean sophisticated) {
		if (sophisticated) {
			return getSophisticatedDefaultInitializationForType(loc, cType);
		} else {
			return getNaiveDefaultInitializationForType(loc, cType);
		}
	}

	private ExpressionResult getNaiveDefaultInitializationForType(final ILocation loc, final CType cType) {
		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {
			return new ExpressionResultBuilder()
					.setLRVal(new RValue(getDefaultValueForSimpleType(loc, cType), cType))
					.build();
		} else if (cType instanceof CStruct) {
			return null;
		} else if (cType instanceof CArray) {
			return null;
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	private ExpressionResult getSophisticatedDefaultInitializationForType(final ILocation loc, final CType cType) {
		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {
			return getNaiveDefaultInitializationForType(loc, cType);
		} else if (cType instanceof CStruct) {
			return null;
		} else if (cType instanceof CArray) {
			return null;
		} else {
			throw new UnsupportedOperationException("missing case?");
		}
	}

	private List<Integer> getConstantDimensions(final CArray cArrayType) {
		if (isVarlength(cArrayType)) {
			throw new IllegalArgumentException("only call this for non-varlength array types");
		}
		final List<Integer> result = new ArrayList<>();
		for (final RValue dimRVal : cArrayType.getDimensions()) {
			final int dimInt = Integer.parseUnsignedInt(((IntegerLiteral) dimRVal.getValue()).getValue());
			result.add(dimInt);
		}
		return result;
	}

	private boolean isVarlength(final CArray cArrayType) {
		for (final RValue dimRVal : cArrayType.getDimensions()) {
			if (!(dimRVal.getValue() instanceof IntegerLiteral)) {
				return true;
			}
		}
		return false;
	}

	private ExpressionResult initCArray(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CArray cArrayType, final InitializerResult initializerConvertedIfAny, final boolean onHeap) {

		assert initializerConvertedIfAny.hasBeenConvertedToTargetType();

		if (doSophisticatedInitialization(initializerConvertedIfAny)) {
			if (onHeap) {
				return initCArrayOnHeapSophisticated(loc, main, (HeapLValue) lhsIfAny, cArrayType,
						initializerConvertedIfAny);
			} else {
				return initCArrayOffHeapSophisticated(loc, main, (LocalLValue) lhsIfAny, cArrayType, initializerConvertedIfAny);
			}
		} else {
			if (onHeap) {
				return initCArrayOnHeapNaive(loc, main, (HeapLValue) lhsIfAny, cArrayType, initializerConvertedIfAny);
			} else {
				return initCArrayOffHeapNaive(loc, main, (LocalLValue) lhsIfAny, cArrayType, initializerConvertedIfAny);
			}
		}
//		final ExpressionResultBuilder initializer = new ExpressionResultBuilder();
//
//		final LocalLValue initializedArray;
//		if (lhsIfAny != null) {
//			initializedArray = lhsIfAny;
//		} else {
////			String initializerValueId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, cArrayType);
////			initializer.addDeclaration(new VariableDeclaration(loc, new Attribute[0], new VarList[] { new Varli }));
////			initializedArray = new LocalLValue(new VariableLHS(loc, identifier), cArrayType);
//			final AuxVarHelper initializerValueAuxVar = CTranslationUtil.makeAuxVarDeclaration(loc, main,
//					SFO.AUXVAR.ARRAYINIT, cArrayType);
//			initializer.addDeclaration(initializerValueAuxVar.getVarDec());
//			initializedArray = new LocalLValue(initializerValueAuxVar.getLhs(), cArrayType);
//			initializer.setLRVal(initializedArray);
////			initializer.setLRVal(new RValue(initializerValueAuxVar.getExp(), cArrayType));
//		}
//
//
//		final Statement arrayInitCall = getInitializerArrayCall(initializedArray, cArrayType);
//
//		return null;
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
	private boolean doSophisticatedInitialization(final InitializerResult initializerIfAny) {
		// TODO Auto-generated method stub
		return false;
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

	private Expression getDefaultValueForSimpleType(final ILocation loc, final CType cType) {
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
	 * Represents all information that is needed to initialize a given expresion with a given initializer.
	 * Is generated from an InitializerResult together with a target CType.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	class InitializerInfo {

		public InitializerInfo(final InitializerResult initializerResult, final CType targetCType) {

		}

	}
}
