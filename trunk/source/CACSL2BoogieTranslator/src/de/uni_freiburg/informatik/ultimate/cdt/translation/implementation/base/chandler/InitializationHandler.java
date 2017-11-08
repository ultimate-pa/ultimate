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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListRecResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Generates Boogie code that models initializations that happen in the C program.
 * Initializations may happen implicitly, e.g., for static variables, or explicitly via an initializer.
 * The "uninitialized" case is not treated here (we havoc each variable at its initialization position, by default).
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
	 * Initializes global variables recursively, according to ISO/IEC 9899:TC3, 6.7.8 §10:<br>
	 * <blockquote cite="http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf"><i>"If an object that has automatic
	 * storage duration is not initialized explicitly, its value is indeterminate. If an object that has static storage
	 * duration is not initialized explicitly, then:
	 * <ul>
	 * <li>if it has pointer type, it is initialized to a null pointer;</li>
	 * <li>if it has arithmetic type, it is initialized to (positive or unsigned) zero;</li>
	 * <li>if it is an aggregate, every member is initialized (recursively) according to these rules;</li>
	 * <li>if it is a union, the first named member is initialized (recursively) according to these rules."</li>
	 * </ul>
	 * </i></blockquote> where (from 6.2.5 Types §21):
	 * <blockquote cite="http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf" ><i>"Arithmetic types and pointer
	 * types are collectively called scalar types. Array and structure types are collectively called aggregate
	 * types."</i></blockquote>
	 *
	 * -- version for Expression that have an identifier in the program, i.e. where onHeap is determined via the
	 * corresponding store in the CHandler --
	 *
	 * @param lhs
	 *            the LeftHandSide to initialize. If this is null, the initializing value is returned in the lrValue of
	 *            the returned ResultExpression which otherwise is null. (Detail: if we initialize something onHeap, lhs
	 *            may not be null)
	 * @param cType
	 *            The CType of the initialized variable
	 *
	 * @return
	 */
	public ExpressionResult initVar(final ILocation loc, final Dispatcher main, final LeftHandSide lhs,
			final CType cType, final ExpressionResult initializerRaw) {

		boolean onHeap = false;
		if (lhs != null && lhs instanceof VariableLHS) {
			onHeap = ((CHandler) main.mCHandler).isHeapVar(((VariableLHS) lhs).getIdentifier());
		}

		LRValue var = null;
		if (onHeap) {
			var = new HeapLValue(new IdentifierExpression(loc, ((VariableLHS) lhs).getIdentifier()), cType);
		} else {
			var = lhs == null ? null : new LocalLValue(lhs, cType);
		}

		if (var == null) {
			return makeVarInitializationNoReturnValue(loc, main, cType, initializerRaw);
		} else {
			return makeVarInitializationWithGivenReturnValue(loc, main, var, cType, initializerRaw);
		}
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
	 * @param cTypeRaw
	 * @param initializerRaw
	 * @return
	 */
	public ExpressionResult initVarNew(final ILocation loc, final Dispatcher main, final LeftHandSide lhsRaw,
			final CType cTypeRaw, final ExpressionResult initializerRaw) {

		boolean onHeap = false;
		if (lhsRaw != null && lhsRaw instanceof VariableLHS) {
			onHeap = ((CHandler) main.mCHandler).isHeapVar(((VariableLHS) lhsRaw).getIdentifier());
		}

		LRValue lhs = null;
		if (onHeap) {
			// lhsRaw must be non-null at this point because of the above code that determined "onHeap"
			lhs = new HeapLValue(new IdentifierExpression(loc, ((VariableLHS) lhsRaw).getIdentifier()), cTypeRaw);
		} else {
			lhs = lhsRaw == null ? null : new LocalLValue(lhsRaw, cTypeRaw);
		}


		return initVarRec(loc, main, cTypeRaw, initializerRaw, onHeap, lhs);
	}

	private ExpressionResult initVarRec(final ILocation loc, final Dispatcher main, final CType cTypeRaw,
			final Result initializerRaw, final boolean onHeap, final LRValue lhs) {
		assert initializerRaw instanceof ExpressionResult || initializerRaw instanceof ExpressionListRecResult;
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer) {
			/*
			 * We are dealing with an initialization of a value with non-struct type.
			 * We construct a builder from the given initializer which will later constitute the initialization code,
			 * i.e, the result of this method
			 * The initializerRaw may already contain some statements and declarations that we need to carry over (for
			 *  example if the C code contained a function call), so we carry those over into the builder.
			 */
			assert !(initializerRaw instanceof ExpressionListRecResult);
			ExpressionResultBuilder initializer = null;
			if (initializerRaw != null ) {
				final ExpressionResult initializerRawSwitched =
						((ExpressionResult) initializerRaw).switchToRValueIfNecessary(main, mMemoryHandler,
								mStructHandler, loc);
				initializerRawSwitched.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

				/*
				 * Conversions need to be applied here (like for a normal assignment), because the rhs of an
				 * initalization may not be of the right type.
				 * Simplest example: "int * i = 0", here the "0" must be converted to the null pointer.
				 */
				main.mCHandler.convert(loc, initializerRawSwitched, cType);

				initializer = new ExpressionResultBuilder();
				initializer.addStatements(initializerRawSwitched.getStatements());
				initializer.addDeclarations(initializerRawSwitched.getDeclarations());
				initializer.addOverapprox(initializerRawSwitched.getOverapprs());
				initializer.putAuxVars(initializerRawSwitched.getAuxVars());
				initializer.setLRVal(initializerRawSwitched.getLrValue());
				assert initializerRawSwitched.otherUnionFields == null || initializerRawSwitched.otherUnionFields.isEmpty();
			}

			return initExpressionWithSimpleType(loc, main, lhs, onHeap, cType, initializer);
//			if (cType instanceof CPrimitive) {
//				return initCPrimitiveOrCEnum(loc, main, lhs, onHeap, cType, initializer);
//			} else if (cType instanceof CEnum) {
//				return initCPrimitiveOrCEnum(loc, main, lhs, onHeap, cType, initializer);
////				return initCEnum(loc, main, lhs, onHeap, (CEnum) cType, initializer);
//			} else if (cType instanceof CPointer) {
//				return initCPrimitiveOrCEnum(loc, main, lhs, onHeap, cType, initializer);
////				return initCPointer(loc, main, lhs, onHeap, (CPointer) cType, initializer);
//			} else {
//				throw new UnsupportedOperationException("missing case for simple CType");
//			}
		} else if (cType instanceof CStruct && onHeap) {
			return initCStructOnHeap(loc, main, lhs, (CStruct) cType, (ExpressionListRecResult) initializerRaw);
		} else if (cType instanceof CStruct && !onHeap) {
			return initCStructOffHeap(loc, main, lhs, (CStruct) cType, (ExpressionListRecResult) initializerRaw);
		} else if (cType instanceof CArray && onHeap) {
			return initCArrayOnHeap(loc, main, (HeapLValue) lhs, (CArray) cType,
					initializerRaw == null ? null : ((ExpressionListRecResult) initializerRaw).list);
		} else if (cType instanceof CArray && !onHeap) {
			return initCArrayOffHeap(loc, main, (LocalLValue) lhs, (CArray) cType,
					initializerRaw == null ? null : ((ExpressionListRecResult) initializerRaw).list);
		} else {
			throw new UnsupportedOperationException("missing case for CType");
		}
	}


	private ExpressionResult initExpressionWithSimpleType(final ILocation loc, final Dispatcher main,
			final LRValue lhsIfAny, final boolean onHeap, final CType cType,
			final ExpressionResultBuilder initializerIfAny) {
		assert cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer;

		final Expression initializationValue;
		final ExpressionResultBuilder initializer;

		if (initializerIfAny != null) {
			/*
			 * There is initialization code in the C program.
			 * Conversions have already been applied by the calling method, so we can just use the value in
			 * initializerIfAny.
			 */
			initializationValue = initializerIfAny.mLrVal.getValue();
			initializer = initializerIfAny;
		} else {
			// there is no initialization code in the C program --> initialize to defaults
			initializationValue = getDefaultValueForSimpleType(loc, cType);
			initializer = new ExpressionResultBuilder();
			initializer.setLRVal(new RValue(initializationValue, cType));
		}

		if (lhsIfAny != null && onHeap) {
			initializer.addStatements(mMemoryHandler.getWriteCall(loc, (HeapLValue) lhsIfAny, initializationValue,
					cType));
		} else if (lhsIfAny != null && !onHeap) {
			final AssignmentStatement assignment =
					new AssignmentStatement(loc,
							new LeftHandSide[] { ((LocalLValue) lhsIfAny).getLHS() },
							new Expression[] { initializationValue });
			addOverApprToStatementAnnots(initializer.mOverappr, assignment);
			initializer.addStatement(assignment);
		}

		return initializer.build();
	}



//	private ExpressionResult initCEnum(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
//			final boolean onHeap, final CEnum cType, final ExpressionResultBuilder initializerIfAny) {
//
//		final Expression initializationValue;
//		final ExpressionResultBuilder initializer;
//
//		if (initializerIfAny != null) {
//			// there is initialization code in the C program
//			initializationValue = initializerIfAny.mLrVal.getValue();
//			initializer = initializerIfAny;
//		} else {
//			// there is no initialization code in the C program --> initialize to defaults
//
//			// default initialization value for an enum the same as for "int"
//			initializationValue = getDefaultValue(loc, new CPrimitive(CPrimitives.INT));
//
//			initializer = new ExpressionResultBuilder();
//			initializer.setLRVal(new RValue(initializationValue, cType));
//		}
//
//		if (lhsIfAny != null && onHeap) {
//			initializer.addStatements(mMemoryHandler.getWriteCall(loc, (HeapLValue) lhsIfAny, initializationValue,
//					cType));
//		} else if (lhsIfAny != null && !onHeap) {
//			final AssignmentStatement assignment =
//					new AssignmentStatement(loc,
//							new LeftHandSide[] { ((LocalLValue) lhsIfAny).getLHS() },
//							new Expression[] { initializationValue });
//			addOverApprToStatementAnnots(initializer.mOverappr, assignment);
//			initializer.addStatement(assignment);
//		}
//
//		return initializer.build();
//	}

//	private ExpressionResult initCPointer(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
//			final boolean onHeap, final CPointer cType, final ExpressionResultBuilder initializerIfAny) {
//
//		final Expression initializationValue;
//		final ExpressionResultBuilder initializer;
//
//		if (initializerIfAny != null) {
//			// there is initialization code in the C program
//			initializationValue = initializerIfAny.mLrVal.getValue();
//			initializer = initializerIfAny;
//		} else {
//			// there is no initialization code in the C program --> initialize to defaults
//			initializationValue = getDefaultValueForSimpleType(loc, cType);
//			initializer = new ExpressionResultBuilder();
//			initializer.setLRVal(new RValue(initializationValue, cType));
//		}
//
//		if (lhsIfAny != null && onHeap) {
//			initializer.addStatements(mMemoryHandler.getWriteCall(loc, (HeapLValue) lhsIfAny, initializationValue,
//					cType));
//		} else if (lhsIfAny != null && !onHeap) {
//			final AssignmentStatement assignment =
//					new AssignmentStatement(loc,
//							new LeftHandSide[] { ((LocalLValue) lhsIfAny).getLHS() },
//							new Expression[] { initializationValue });
//			addOverApprToStatementAnnots(initializer.mOverappr, assignment);
//			initializer.addStatement(assignment);
//		}
//
//		return initializer.build();
//
//
//		// nolhs
////		if (initializer == null) {
////			rhs = mExpressionTranslation.constructNullPointer(loc);
////		} else {
////			final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
////			if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
////				rhs = initializer.lrVal.getValue();
////			} else if (initializerUnderlyingType instanceof CPrimitive
////					&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
////				final BigInteger pointerOffsetValue =
////						mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
////				if (pointerOffsetValue == null) {
////					throw new IllegalArgumentException("unable to understand " + initializer.lrVal);
////				}
////				if (pointerOffsetValue.equals(BigInteger.ZERO)) {
////					rhs = mExpressionTranslation.constructNullPointer(loc);
////				} else {
////					final BigInteger pointerBaseValue = BigInteger.ZERO;
////					rhs = mExpressionTranslation.constructPointerForIntegerValues(loc, pointerBaseValue,
////							pointerOffsetValue);
////				}
////			} else {
////				throw new AssertionError(
////						"trying to initialize a pointer with something different from int and pointer");
////			}
////		}
////
////		lrVal = new RValue(rhs, lCType);
//
//		// lhs
////		if (initializer == null) {
////			rhs = mExpressionTranslation.constructNullPointer(loc);
////		} else {
////			final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
////			if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
////				rhs = initializer.lrVal.getValue();
////			} else if (initializerUnderlyingType instanceof CPrimitive
////					&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
////				final BigInteger offsetValue =
////						mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
////				if (offsetValue.equals(BigInteger.ZERO)) {
////					rhs = mExpressionTranslation.constructNullPointer(loc);
////				} else {
////					final Expression base = mExpressionTranslation.constructLiteralForIntegerType(loc,
////							mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
////					final Expression offset = mExpressionTranslation.constructLiteralForIntegerType(loc,
////							mExpressionTranslation.getCTypeOfPointerComponents(), offsetValue);
////					rhs = MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
////				}
////			} else {
////				throw new AssertionError(
////						"trying to initialize a pointer with something different from int and pointer");
////			}
////		}
////		if (onHeap) {
////			stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, lCType));
////		} else {
////			assert lhs != null;
////			final AssignmentStatement assignment =
////					new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
////			addOverApprToStatementAnnots(overappr, assignment);
////			stmt.add(assignment);
////		}
//	}

	private ExpressionResult initCStructOffHeap(final ILocation loc, final Dispatcher main, final LRValue lhsIfAny,
			final CStruct cType, final ExpressionListRecResult initializerRaw) {
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
				final ExpressionListRecResult	currentFieldInitializerRawIfAny = null; //TODO

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
			final CStruct cType, final ExpressionListRecResult initializerRaw) {


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

	private ExpressionResult initCArrayOnHeap(final ILocation loc, final Dispatcher main, final HeapLValue lhsIfAny,
			final CArray cType, final List<ExpressionListRecResult> initializerIfAny) {

		return null;
	}

	private ExpressionResult initCArrayOffHeap(final ILocation loc, final Dispatcher main, final LocalLValue lhsIfAny,
			final CArray cArrayType, final List<ExpressionListRecResult> initializerIfAny) {

		final ExpressionResultBuilder initializer = new ExpressionResultBuilder();

		final LocalLValue initializedArray;
		if (lhsIfAny != null) {
			initializedArray = lhsIfAny;
		} else {
//			String initializerValueId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, cArrayType);
//			initializer.addDeclaration(new VariableDeclaration(loc, new Attribute[0], new VarList[] { new Varli }));
//			initializedArray = new LocalLValue(new VariableLHS(loc, identifier), cArrayType);
			final AuxVarInfo initializerValueAuxVar = CTranslationUtil.makeAuxVarDeclaration(loc, main,
					SFO.AUXVAR.ARRAYINIT, cArrayType);
			initializer.addDeclaration(initializerValueAuxVar.getVarDec());
			initializedArray = new LocalLValue(initializerValueAuxVar.getLhs(), cArrayType);
			initializer.setLRVal(initializedArray);
//			initializer.setLRVal(new RValue(initializerValueAuxVar.getExp(), cArrayType));
		}


		final Statement arrayInitCall = getInitializerArrayCall(initializedArray, cArrayType);


//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(cType.getDimensions()[0]);
//		if (dimBigInteger == null) {
//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
//		}
//		final int currentSizeInt = dimBigInteger.intValue();

//		// iterate over the dimensions outermost first
//		for (int dim = dimensions.length - 1; dim >= 0; dim --) {



//		// iterate over the dimensions innermost first
////		for (int dim = 0; dim < dimensions.length; dim++) {
//		for (int dim = dimensions.length - 1; dim >= 0; dim --) {
//
//			final RValue currentArrayDim = dimensions[dim];
////
//			final String iteratorVariableName = SFO.AUXVAR.ARRAYINITITERATOR + "_" + dim;
//			final Expression currentIteratorVariable = new IdentifierExpression(loc, iteratorVariableName);
////
////			final Expression currentCondition = null;
//			final List<Statement> currentBody= null;
////			final WhileStatement currentLoop = new WhileStatement(loc, currentCondition,
////					new LoopInvariantSpecification[0], currentBody);
//
////			final Statement currentLoop = createForLoop(0, currentArrayDim.getValue(), currentIteratorVariable,
////					currentBody);
//		}

		return null;
//		if (dimensions.length == 1) {
//			RValue val = null;
//
//			for (int i = 0; i < currentSizeInt; i++) {
//				if (list != null && list.size() > i && list.get(i).lrVal != null) {
//					// we have a value to initialize with
//					final CType valueType = arrayType.getValueType().getUnderlyingType();
//					main.mCHandler.convert(loc, list.get(i), valueType);
//					val = (RValue) list.get(i).lrVal;
//					decl.addAll(list.get(i).decl);
//					auxVars.putAll(list.get(i).auxVars);
//					stmt.addAll(list.get(i).stmt);
//					overApp.addAll(list.get(i).overappr);
//				} else {
//					// do default initialization
//					final CType valueType = arrayType.getValueType().getUnderlyingType();
//
//					if (valueType instanceof CArray) {
//						throw new AssertionError(
//								"this should not be the case as we are in the inner/outermost array right??");
//					} else if (valueType instanceof CStruct) {
//						final ExpressionResult sInit =
//								makeStructConstructorFromRERL(main, loc, null, (CStruct) valueType);
//						stmt.addAll(sInit.stmt);
//						decl.addAll(sInit.decl);
//						auxVars.putAll(sInit.auxVars);
//						overApp.addAll(sInit.overappr);
//						val = (RValue) sInit.lrVal;
//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer
//							|| valueType instanceof CEnum) {
//						val = (RValue) main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType,
//								null).lrVal;
//					} else {
//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
//					}
//				}
//				Expression[] newIndices = null;
//				LeftHandSide newLHS = null;
//				final CPrimitive indexType = (CPrimitive) dimensions[0].getCType();
//				final Expression index =
//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
//				if (innerArrayAccessLHS instanceof ArrayLHS) {
//					final ArrayList<Expression> innerIndices =
//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
//					innerIndices.add(index);
//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
//				} else {
//					newIndices = new Expression[] { index };
//					newLHS = innerArrayAccessLHS;
//				}
//
//				final ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { arrayAccessLHS },
//						new Expression[] { val.getValue() });
//				addOverApprToStatementAnnots(overApp, assignment);
//				stmt.add(assignment);
//			}
//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
//		} else {
//			for (int i = 0; i < currentSizeInt; i++) {
//
//				Expression[] newIndices = null;
//				LeftHandSide newLHS = null;
//
//				// 2015-10-24 Matthias: I don't understand where I can take the
//				// type of the index from. As a workaround I take signed int.
//				final CPrimitive indexType = new CPrimitive(CPrimitives.INT);
//				final Expression index =
//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
//				if (innerArrayAccessLHS instanceof ArrayLHS) {
//					final ArrayList<Expression> innerIndices =
//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
//					innerIndices.add(index);
//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
//				} else {
//					newIndices = new Expression[] { index };
//					newLHS = innerArrayAccessLHS;
//				}
//
//				final List<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
//				innerDims.remove(0);// TODO ??
//				final CArray innerArrayType =
//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
//
//				final List<ExpressionListRecResult> listRecCall;
//				if (list == null) {
//					listRecCall = null;
//				} else if (list.size() - 1 < i) {
//					listRecCall = null;
//				} else {
//					listRecCall = list.get(i).list;
//				}
//				final ExpressionResult initRex =
//						initBoogieArray(main, loc, listRecCall, new ArrayLHS(loc, newLHS, newIndices), innerArrayType);
//				stmt.addAll(initRex.stmt);
//				decl.addAll(initRex.decl);
//				auxVars.putAll(initRex.auxVars);
//				overApp.addAll(initRex.overappr);
//			}
//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
//		}
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
	private Statement getInitializerArrayCall(final Expression lhs, final CArray arrayType) {
		mDeclareArrayInitializationFunction = true;

		// TODO Auto-generated method stub
		return null;
	}


	//	/**
	//	 * Helper for variable initialization. This version does not take any form of the initialized variable as an
	//	 * argument but instead returns a ResultExpression with an lrValue that can be stored in such a variable.
	//	 */
	//	private ExpressionResult makeVarInitializationNoReturnValue(final ILocation loc, final Dispatcher main,
	//			final CType cType, final ExpressionResult initializerRaw) {
	//		final CType lCType = cType.getUnderlyingType();
	//
	//		final ArrayList<Statement> stmt = new ArrayList<Statement>();
	//		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
	//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
	//		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
	//
	//		// if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
	//		// carry over
	//		ExpressionResult initializer = null;
	//		if (initializerRaw != null) {
	//			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
	//			stmt.addAll(initializer.stmt);
	//			decl.addAll(initializer.decl);
	//			overappr.addAll(initializer.overappr);
	//			auxVars.putAll(initializer.auxVars);
	//		}
	//
	//		final LRValue lrVal;
	//		final Expression rhs;
	//		if (lCType instanceof CPrimitive) {
	//			if (initializer == null) {
	//				final CPrimitive lCPrimitive = (CPrimitive) lCType;
	//				switch (lCPrimitive.getGeneralType()) {
	//				case INTTYPE:
	//					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, lCPrimitive, BigInteger.ZERO);
	//					break;
	//				case FLOATTYPE:
	//					rhs = mExpressionTranslation.constructLiteralForFloatingType(loc, lCPrimitive, BigDecimal.ONE);
	//					break;
	//				case VOID:
	//					throw new AssertionError("cannot initialize something that has type void");
	//				default:
	//					throw new AssertionError("unknown category of type");
	//				}
	//			} else {
	//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
	//				main.mCHandler.convert(loc, initializer, lCType);
	//				rhs = initializer.lrVal.getValue();
	//			}
	//			lrVal = new RValue(rhs, lCType);
	//		} else if (lCType instanceof CPointer) {
	//			if (initializer == null) {
	//				rhs = mExpressionTranslation.constructNullPointer(loc);
	//			} else {
	//				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
	//				if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
	//					rhs = initializer.lrVal.getValue();
	//				} else if (initializerUnderlyingType instanceof CPrimitive
	//						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
	//					final BigInteger pointerOffsetValue =
	//							mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
	//					if (pointerOffsetValue == null) {
	//						throw new IllegalArgumentException("unable to understand " + initializer.lrVal);
	//					}
	//					if (pointerOffsetValue.equals(BigInteger.ZERO)) {
	//						rhs = mExpressionTranslation.constructNullPointer(loc);
	//					} else {
	//						final BigInteger pointerBaseValue = BigInteger.ZERO;
	//						rhs = mExpressionTranslation.constructPointerForIntegerValues(loc, pointerBaseValue,
	//								pointerOffsetValue);
	//					}
	//				} else {
	//					throw new AssertionError(
	//							"trying to initialize a pointer with something different from int and pointer");
	//				}
	//			}
	//
	//			lrVal = new RValue(rhs, lCType);
	//		} else if (lCType instanceof CArray) {
	//			final VariableLHS lhs = null;
	//
	//			if (initializer == null) {
	//				final ExpressionResult aInit = initBoogieArray(main, loc, null, lhs, (CArray) lCType);
	//				stmt.addAll(aInit.stmt);
	//				decl.addAll(aInit.decl);
	//				auxVars.putAll(aInit.auxVars);
	//			} else if (initializer instanceof ExpressionListRecResult) {
	//				final ExpressionResult aInit =
	//						initBoogieArray(main, loc, ((ExpressionListRecResult) initializer).list, lhs, (CArray) lCType);
	//				stmt.addAll(aInit.stmt);
	//				decl.addAll(aInit.decl);
	//				auxVars.putAll(aInit.auxVars);
	//			} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
	//																	// corresponding aux vars
	//				// stmt.addAll(initializer.stmt);
	//				// decl.addAll(initializer.decl);
	//				// auxVars.putAll(initializer.auxVars);
	//			} else {
	//				assert false;
	//			}
	//			// }
	//			assert lhs != null;
	//			lrVal = null;
	//		} else if (lCType instanceof CStruct) {
	//			final CStruct structType = (CStruct) lCType;
	//
	//			final ExpressionResult scRex =
	//					makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
	//
	//			stmt.addAll(scRex.stmt);
	//			decl.addAll(scRex.decl);
	//			overappr.addAll(scRex.overappr);
	//			auxVars.putAll(scRex.auxVars);
	//			rhs = null;
	//			lrVal = new RValue(rhs, lCType);
	//		} else if (lCType instanceof CEnum) {
	//			if (initializer == null) {
	//				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
	//						BigInteger.ZERO);
	//			} else {
	//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
	//				rhs = initializer.lrVal.getValue();
	//			}
	//			lrVal = new RValue(rhs, lCType);
	//		} else {
	//			final String msg = "Unknown type - don't know how to initialize!";
	//			throw new UnsupportedSyntaxException(loc, msg);
	//		}
	//		assert CHandler.isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
	//
	//		// lrVal is null in case we got a lhs to assign to, the initializing value otherwise
	//		return new ExpressionResult(stmt, lrVal, decl, auxVars, overappr);
	//	}
	
	//	/**
	//	 * Same as other initVar but with an LRValue as argument, not a LHS if var is a HeapLValue, something on Heap is
	//	 * initialized, if it is a LocalLValue something off the Heap is initialized
	//	 */
	//	private ExpressionResult makeVarInitializationWithGivenReturnValue(final ILocation loc, final Dispatcher main, final LRValue var, final CType cType,
	//			final ExpressionResult initializerRaw) {
	//		assert var != null;
	//
	//		final boolean onHeap = var instanceof HeapLValue;
	//
	//		final CType lCType = cType.getUnderlyingType();
	//
	//		final ArrayList<Statement> stmt = new ArrayList<Statement>();
	//		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
	//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
	//		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
	//
	//		// if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
	//		// carry over
	//		ExpressionResult initializer = null;
	//		if (initializerRaw != null) {
	//			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
	//			stmt.addAll(initializer.stmt);
	//			decl.addAll(initializer.decl);
	//			overappr.addAll(initializer.overappr);
	//			auxVars.putAll(initializer.auxVars);
	//		}
	//
	//		VariableLHS lhs = null;
	//		if (var instanceof LocalLValue) {
	//			lhs = (VariableLHS) ((LocalLValue) var).getLHS();
	//		}
	//		Expression rhs = null;
	//		if (lCType instanceof CPrimitive) {
	//			switch (((CPrimitive) lCType).getGeneralType()) {
	//			case INTTYPE:
	//				if (initializer == null) {
	//					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, (CPrimitive) lCType,
	//							BigInteger.ZERO);
	//				} else {
	//					initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
	//					main.mCHandler.convert(loc, initializer, lCType);
	//					rhs = initializer.lrVal.getValue();
	//				}
	//				break;
	//			case FLOATTYPE:
	//				if (mExpressionTranslation instanceof BitvectorTranslation) {
	//					if (initializer == null) {
	//						if (((CPrimitive) lCType).getType().equals(CPrimitives.FLOAT)) {
	//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
	//						} else if (((CPrimitive) lCType).getType().equals(CPrimitives.DOUBLE)) {
	//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
	//						} else if (((CPrimitive) lCType).getType().equals(CPrimitives.LONGDOUBLE)) {
	//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
	//						} else {
	//							throw new UnsupportedOperationException("UNsopported Floating Type");
	//						}
	//					} else {
	//						main.mCHandler.convert(loc, initializer, lCType);
	//						rhs = initializer.lrVal.getValue();
	//					}
	//				} else {
	//					if (initializer == null) {
	//						rhs = new RealLiteral(loc, SFO.NR0F);
	//					} else {
	//						main.mCHandler.convert(loc, initializer, lCType);
	//						rhs = initializer.lrVal.getValue();
	//					}
	//				}
	//				break;
	//			case VOID:
	//			default:
	//				throw new AssertionError("unknown type to init");
	//			}
	//			if (onHeap) {
	//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, cType));
	//			} else {
	//				assert lhs != null;
	//				final AssignmentStatement assignment =
	//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
	//				addOverApprToStatementAnnots(overappr, assignment);
	//				stmt.add(assignment);
	//			}
	//		} else if (lCType instanceof CPointer) {
	//			if (initializer == null) {
	//				rhs = mExpressionTranslation.constructNullPointer(loc);
	//			} else {
	//				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
	//				if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
	//					rhs = initializer.lrVal.getValue();
	//				} else if (initializerUnderlyingType instanceof CPrimitive
	//						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
	//					final BigInteger offsetValue =
	//							mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
	//					if (offsetValue.equals(BigInteger.ZERO)) {
	//						rhs = mExpressionTranslation.constructNullPointer(loc);
	//					} else {
	//						final Expression base = mExpressionTranslation.constructLiteralForIntegerType(loc,
	//								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
	//						final Expression offset = mExpressionTranslation.constructLiteralForIntegerType(loc,
	//								mExpressionTranslation.getCTypeOfPointerComponents(), offsetValue);
	//						rhs = MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
	//					}
	//				} else {
	//					throw new AssertionError(
	//							"trying to initialize a pointer with something different from int and pointer");
	//				}
	//			}
	//			if (onHeap) {
	//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, lCType));
	//			} else {
	//				assert lhs != null;
	//				final AssignmentStatement assignment =
	//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
	//				addOverApprToStatementAnnots(overappr, assignment);
	//				stmt.add(assignment);
	//			}
	//		} else if (lCType instanceof CArray) {
	//
	//			if (onHeap) {
	//				final IdentifierExpression arrayAddress = (IdentifierExpression) ((HeapLValue) var).getAddress();
	//				lhs = new VariableLHS(arrayAddress.getLocation(), arrayAddress.getIdentifier());
	//
	//				// done in simpleDec
	//				// CallStatement mallocRex = mMemoryHandler.getMallocCall(main, mFunctionHandler,
	//				// mMemoryHandler.calculateSizeOf(lCType, loc), new LocalLValue(lhs, cType), loc);
	//				// stmt.add(mallocRex);
	//
	//				if (initializer == null) {
	//					final ExpressionResult aInit = initArrayOnHeap(main, loc, null, arrayAddress, (CArray) lCType);
	//					stmt.addAll(aInit.stmt);
	//					decl.addAll(aInit.decl);
	//					auxVars.putAll(aInit.auxVars);
	//				} else if (initializer instanceof ExpressionListRecResult) {
	//					final ExpressionResult aInit = initArrayOnHeap(main, loc,
	//							((ExpressionListRecResult) initializer).list, arrayAddress, (CArray) lCType);
	//					stmt.addAll(aInit.stmt);
	//					decl.addAll(aInit.decl);
	//					auxVars.putAll(aInit.auxVars);
	//				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
	//																		// corresponding aux vars
	//					// stmt.addAll(initializer.stmt);
	//					// decl.addAll(initializer.decl);
	//					// auxVars.putAll(initializer.auxVars);
	//				} else {
	//					assert false;
	//				}
	//
	//			} else { // not on Heap
	//				ExpressionResult initRex = null;
	//				if (initializer == null) {
	//					initRex = initBoogieArray(main, loc, null, lhs, (CArray) lCType);
	//				} else if (initializer instanceof ExpressionListRecResult) {
	//					initRex = initBoogieArray(main, loc, ((ExpressionListRecResult) initializer).list, lhs,
	//							(CArray) lCType);
	//				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
	//																		// corresponding aux vars
	//					// stmt.addAll(initializer.stmt);
	//					// decl.addAll(initializer.decl);
	//					// auxVars.putAll(initializer.auxVars);
	//				} else {
	//					assert false;
	//				}
	//				if (initRex != null) {
	//					stmt.addAll(initRex.stmt);
	//					decl.addAll(initRex.decl);
	//					auxVars.putAll(initRex.auxVars);
	//				}
	//			}
	//			assert lhs != null;
	//		} else if (lCType instanceof CStruct) {
	//			final CStruct structType = (CStruct) lCType;
	//
	//			if (onHeap) {
	//				assert var != null;
	//				final ExpressionResult heapWrites = initStructOnHeapFromRERL(main, loc, ((HeapLValue) var).getAddress(),
	//						(ExpressionListRecResult) initializer, structType);
	//
	//				stmt.addAll(heapWrites.stmt);
	//				decl.addAll(heapWrites.decl);
	//				overappr.addAll(heapWrites.overappr);
	//				auxVars.putAll(heapWrites.auxVars);
	//			} else {
	//				final ExpressionResult scRex =
	//						makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
	//
	//				stmt.addAll(scRex.stmt);
	//				decl.addAll(scRex.decl);
	//				overappr.addAll(scRex.overappr);
	//				auxVars.putAll(scRex.auxVars);
	//
	//				assert lhs != null;
	//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
	//						new Expression[] { scRex.lrVal.getValue() });
	//				addOverApprToStatementAnnots(overappr, assignment);
	//				stmt.add(assignment);
	//			}
	//		} else if (lCType instanceof CEnum) {
	//			if (initializer == null) {
	//				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc,
	//						new CPrimitive(CPrimitive.CPrimitives.INT), BigInteger.ZERO);
	//			} else {
	//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
	//				rhs = initializer.lrVal.getValue();
	//			}
	//			if (onHeap) {
	//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, cType));
	//			} else {
	//				assert lhs != null;
	//				final Statement assignment =
	//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
	//				addOverApprToStatementAnnots(overappr, assignment);
	//				stmt.add(assignment);
	//			}
	//		} else {
	//			final String msg = "Unknown type - don't know how to initialize!";
	//			throw new UnsupportedSyntaxException(loc, msg);
	//		}
	//		// assert (CHandler.isAuxVarMapcomplete(main, decl, auxVars));
	//
	//		return new ExpressionResult(stmt, null, decl, auxVars, overappr);
	//	}
	
		//	/**
		//	 * Initializes an array that lies on heap, either with some given values or to its default values.
		//	 *
		//	 * @param list
		//	 *            The values that the array should be initialized with, null for default init
		//	 * @param startAddress
		//	 *            The address on the heap that the array starts at
		//	 * @param arrayType
		//	 *            The type of the array (containing its size and value type)
		//	 * @return a list of statements that do the initialization
		//	 */
		//	private ExpressionResult initArrayOnHeap(final Dispatcher main, final ILocation loc,
		//			final List<ExpressionListRecResult> list, final Expression startAddress, final CArray arrayType) {
		//		final List<Statement> stmt = new ArrayList<>();
		//		final List<Declaration> decl = new ArrayList<>();
		//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		//		final List<Overapprox> overApp = new ArrayList<>();
		//
		//		final Expression sizeOfCell = mMemoryHandler.calculateSizeOf(loc, arrayType.getValueType());
		//		final RValue[] dimensions = arrayType.getDimensions();
		//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
		//		if (dimBigInteger == null) {
		//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		//		}
		//		final int currentSizeInt = dimBigInteger.intValue();
		//
		//		Expression newStartAddressBase = null;
		//		Expression newStartAddressOffset = null;
		//		if (startAddress instanceof StructConstructor) {
		//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
		//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		//		} else {
		//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
		//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		//		}
		//
		//		if (dimensions.length == 1) {
		//			// RValue val = null;
		//
		//			for (int i = 0; i < currentSizeInt; i++) {
		//				CType valueType = arrayType.getValueType().getUnderlyingType();
		//				if (valueType instanceof CEnum) {
		//					valueType = new CPrimitive(CPrimitives.INT);
		//				}
		//
		//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
		//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
		//				Expression writeOffset =
		//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
		//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), sizeOfCell,
		//								mExpressionTranslation.getCTypeOfPointerComponents());
		//
		//				writeOffset = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
		//						newStartAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(), writeOffset,
		//						mExpressionTranslation.getCTypeOfPointerComponents());
		//
		//				final Expression writeLocation =
		//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, writeOffset, loc);
		//
		//				// TODO: we may need to pass statements, decls, ...
		//				if (list != null && list.size() > i && list.get(i).getLrVal() != null) {
		//					final RValue val = (RValue) list.get(i).getLrVal();
		//					decl.addAll(list.get(i).getDeclarations());
		//					auxVars.putAll(list.get(i).getAuxVars());
		//					stmt.addAll(list.get(i).getStatements());
		//					overApp.addAll(list.get(i).getOverapprs());
		//					stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
		//							val.getValue(), val.getCType()));
		//				} else {
		//					if (valueType instanceof CArray) {
		//						throw new AssertionError(
		//								"this should not be the case as we are in the inner/outermost array right??");
		//					} else if (valueType instanceof CStruct) {
		//						final ExpressionResult sInit = initStructOnHeapFromRERL(main, loc, writeLocation,
		//								list != null && list.size() > i ? list.get(i) : null, (CStruct) valueType);
		//						stmt.addAll(sInit.stmt);
		//						decl.addAll(sInit.decl);
		//						auxVars.putAll(sInit.auxVars);
		//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer) {
		//						final ExpressionResult pInit =
		//								main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType, null);
		//						assert pInit.stmt.isEmpty() && pInit.decl.isEmpty() && pInit.auxVars.isEmpty();
		//						final RValue val = (RValue) pInit.lrVal;
		//						stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
		//								val.getValue(), val.getCType()));
		//					} else {
		//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
		//					}
		//				}
		//			}
		//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		//		} else {
		//			for (int i = 0; i < currentSizeInt; i++) {
		//				Expression newStartAddressOffsetInner = newStartAddressOffset;
		//
		//				Expression blockOffset = sizeOfCell;
		//				for (int j = 1; j < dimensions.length; j++) {
		//					blockOffset =
		//							mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
		//									dimensions[j].getValue(), (CPrimitive) dimensions[j].getCType(), blockOffset,
		//									mExpressionTranslation.getCTypeOfPointerComponents());
		//				}
		//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
		//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
		//				blockOffset =
		//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
		//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), blockOffset,
		//								mExpressionTranslation.getCTypeOfPointerComponents());
		//
		//				newStartAddressOffsetInner =
		//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
		//								newStartAddressOffsetInner, mExpressionTranslation.getCTypeOfPointerComponents(),
		//								blockOffset, mExpressionTranslation.getCTypeOfPointerComponents());
		//
		//				final ArrayList<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
		//				innerDims.remove(0);// TODO ??
		//				final CArray innerArrayType =
		//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
		//
		//				final ExpressionResult initRex = initArrayOnHeap(main, loc, list != null ? list.get(i).list : null,
		//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffsetInner,
		//								loc),
		//						innerArrayType);
		//				stmt.addAll(initRex.stmt);
		//				decl.addAll(initRex.decl);
		//				auxVars.putAll(initRex.auxVars);
		//				overApp.addAll(initRex.overappr);
		//			}
		//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		//		}
		//	}
		
		//	/**
		//	 * Initializes an array that is represented as a boogie array, either with some given values or to its default
		//	 * values.
		//	 *
		//	 * @param list
		//	 *            The values that the array should be initialized with, null for default init
		//	 * @param innerArrayAccessLHS
		//	 *            Something representing the array that is to be initialized currently (in case of a nested array this
		//	 *            may again represent an arrayAccess, otherwise the array identifier)
		//	 * @param arrayType
		//	 *            The type of the array (containing its size and value type)
		//	 * @return a list of statements that do the initialization
		//	 */
		//	private ExpressionResult initBoogieArray(final Dispatcher main, final ILocation loc,
		//			final List<ExpressionListRecResult> list, final LeftHandSide innerArrayAccessLHS, final CArray arrayType) {
		//		final List<Statement> stmt = new ArrayList<Statement>();
		//		final List<Declaration> decl = new ArrayList<>();
		//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		//		final List<Overapprox> overApp = new ArrayList<>();
		//
		//		final RValue[] dimensions = arrayType.getDimensions();
		//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
		//		if (dimBigInteger == null) {
		//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		//		}
		//		final int currentSizeInt = dimBigInteger.intValue();
		//
		//		if (dimensions.length == 1) {
		//			RValue val = null;
		//
		//			for (int i = 0; i < currentSizeInt; i++) {
		//				if (list != null && list.size() > i && list.get(i).lrVal != null) {
		//					// we have a value to initialize with
		//					final CType valueType = arrayType.getValueType().getUnderlyingType();
		//					main.mCHandler.convert(loc, list.get(i), valueType);
		//					val = (RValue) list.get(i).lrVal;
		//					decl.addAll(list.get(i).decl);
		//					auxVars.putAll(list.get(i).auxVars);
		//					stmt.addAll(list.get(i).stmt);
		//					overApp.addAll(list.get(i).overappr);
		//				} else {
		//					// do default initialization
		//					final CType valueType = arrayType.getValueType().getUnderlyingType();
		//
		//					if (valueType instanceof CArray) {
		//						throw new AssertionError(
		//								"this should not be the case as we are in the inner/outermost array right??");
		//					} else if (valueType instanceof CStruct) {
		//						final ExpressionResult sInit =
		//								makeStructConstructorFromRERL(main, loc, null, (CStruct) valueType);
		//						stmt.addAll(sInit.stmt);
		//						decl.addAll(sInit.decl);
		//						auxVars.putAll(sInit.auxVars);
		//						overApp.addAll(sInit.overappr);
		//						val = (RValue) sInit.lrVal;
		//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer
		//							|| valueType instanceof CEnum) {
		//						val = (RValue) main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType,
		//								null).lrVal;
		//					} else {
		//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
		//					}
		//				}
		//				Expression[] newIndices = null;
		//				LeftHandSide newLHS = null;
		//				final CPrimitive indexType = (CPrimitive) dimensions[0].getCType();
		//				final Expression index =
		//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
		//				if (innerArrayAccessLHS instanceof ArrayLHS) {
		//					final ArrayList<Expression> innerIndices =
		//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
		//					innerIndices.add(index);
		//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
		//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
		//				} else {
		//					newIndices = new Expression[] { index };
		//					newLHS = innerArrayAccessLHS;
		//				}
		//
		//				final ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
		//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { arrayAccessLHS },
		//						new Expression[] { val.getValue() });
		//				addOverApprToStatementAnnots(overApp, assignment);
		//				stmt.add(assignment);
		//			}
		//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		//		} else {
		//			for (int i = 0; i < currentSizeInt; i++) {
		//
		//				Expression[] newIndices = null;
		//				LeftHandSide newLHS = null;
		//
		//				// 2015-10-24 Matthias: I don't understand where I can take the
		//				// type of the index from. As a workaround I take signed int.
		//				final CPrimitive indexType = new CPrimitive(CPrimitives.INT);
		//				final Expression index =
		//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
		//				if (innerArrayAccessLHS instanceof ArrayLHS) {
		//					final ArrayList<Expression> innerIndices =
		//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
		//					innerIndices.add(index);
		//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
		//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
		//				} else {
		//					newIndices = new Expression[] { index };
		//					newLHS = innerArrayAccessLHS;
		//				}
		//
		//				final List<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
		//				innerDims.remove(0);// TODO ??
		//				final CArray innerArrayType =
		//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
		//
		//				final List<ExpressionListRecResult> listRecCall;
		//				if (list == null) {
		//					listRecCall = null;
		//				} else if (list.size() - 1 < i) {
		//					listRecCall = null;
		//				} else {
		//					listRecCall = list.get(i).list;
		//				}
		//				final ExpressionResult initRex =
		//						initBoogieArray(main, loc, listRecCall, new ArrayLHS(loc, newLHS, newIndices), innerArrayType);
		//				stmt.addAll(initRex.stmt);
		//				decl.addAll(initRex.decl);
		//				auxVars.putAll(initRex.auxVars);
		//				overApp.addAll(initRex.overappr);
		//			}
		//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		//		}
		//		// return arrayWrites;
		//	}
		//
		//	/**
		//	 * Generate the write calls for the initialization of the struct onHeap.
		//	 */
		//	private ExpressionResult initStructOnHeapFromRERL(final Dispatcher main, final ILocation loc,
		//			final Expression startAddress, final ExpressionListRecResult rerlIn, final CStruct structType) {
		//		ExpressionListRecResult rerl = null;
		//		if (rerlIn == null) {
		//			rerl = new ExpressionListRecResult();
		//		} else {
		//			rerl = rerlIn;
		//		}
		//
		//		if (rerl.lrVal != null) {// we have an identifier (or sth else too?)
		//			final ExpressionResult writes = new ExpressionResult((RValue) null);
		//			final ArrayList<Statement> writeCalls =
		//					mMemoryHandler.getWriteCall(loc, new HeapLValue(startAddress, rerl.lrVal.getCType()),
		//							((RValue) rerl.lrVal).getValue(), rerl.lrVal.getCType());
		//			writes.stmt.addAll(writeCalls);
		//			return writes;
		//		}
		//
		//		Expression newStartAddressBase = null;
		//		Expression newStartAddressOffset = null;
		//		if (startAddress instanceof StructConstructor) {
		//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
		//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		//		} else {
		//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
		//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		//		}
		//
		//		// everything for the new Result
		//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
		//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
		//
		//		final String[] fieldIds = structType.getFieldIds();
		//		final CType[] fieldTypes = structType.getFieldTypes();
		//
		//		final boolean isUnion = structType instanceof CUnion;
		//		// in a union, only one field of the underlying struct may be initialized
		//		// we do the first, if no fieldname is given, this variable stores whether
		//		// we already initialized a field
		//		boolean unionAlreadyInitialized = false;
		//
		//		for (int i = 0; i < fieldIds.length; i++) {
		//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
		//
		//			final Expression fieldAddressBase = newStartAddressBase;
		//			final Expression fieldAddressOffset =
		//					mStructHandler.computeStructFieldOffset(mMemoryHandler, loc, i, newStartAddressOffset, structType);
		//			final StructConstructor fieldPointer =
		//					MemoryHandler.constructPointerFromBaseAndOffset(fieldAddressBase, fieldAddressOffset, loc);
		//			final HeapLValue fieldHlv = new HeapLValue(fieldPointer, underlyingFieldType);
		//
		//			ExpressionResult fieldWrites = null;
		//
		//			if (isUnion) {
		//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
		//				// TODO: maybe not use auxiliary variables so lavishly
		//				if (!unionAlreadyInitialized && rerl.list.size() == 1
		//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
		//								|| fieldIds[i].equals(rerl.list.get(0).field))
		//						&& (underlyingFieldType instanceof CStruct
		//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
		//					// use the value from the rerl to initialize the union
		//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
		//							rerl.list.get(0));
		//					unionAlreadyInitialized = true;
		//				} else {
		//					// fill in the uninitialized aux variable
		//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
		//
		//					fieldWrites = new ExpressionResult((RValue) null);
		//					fieldWrites.stmt.addAll(mMemoryHandler.getWriteCall(loc, fieldHlv,
		//							new IdentifierExpression(loc, tmpId), underlyingFieldType));
		//					final VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0],
		//							new VarList[] { new VarList(loc, new String[] { tmpId },
		//									main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
		//					fieldWrites.decl.add(auxVarDec);
		//					fieldWrites.auxVars.put(auxVarDec, loc);
		//				}
		//
		//			} else {
		//				if (underlyingFieldType instanceof CPrimitive) {
		//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
		//							i < rerl.list.size() ? rerl.list.get(i) : null);
		//				} else if (underlyingFieldType instanceof CPointer) {
		//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
		//							i < rerl.list.size() ? rerl.list.get(i) : null);
		//				} else if (underlyingFieldType instanceof CArray) {
		//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
		//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
		//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
		//							new LinkedHashMap<VariableDeclaration, ILocation>();
		//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
		//
		//					ExpressionListRecResult arrayInitRerl = null;
		//					if (i < rerl.list.size()) {
		//						arrayInitRerl = rerl.list.get(i);
		//					}
		//
		//					final ExpressionResult aInit =
		//							initArrayOnHeap(main, loc, arrayInitRerl == null ? null : arrayInitRerl.list, fieldPointer,
		//									(CArray) underlyingFieldType);
		//					fieldStmt.addAll(aInit.stmt);
		//					fieldDecl.addAll(aInit.decl);
		//					fieldAuxVars.putAll(aInit.auxVars);
		//					fieldOverApp.addAll(aInit.overappr);
		//
		//					fieldWrites = new ExpressionResult(fieldStmt, null, fieldDecl, fieldAuxVars, fieldOverApp);
		//				} else if (underlyingFieldType instanceof CEnum) {
		//					// like CPrimitive (?)
		//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
		//							i < rerl.list.size() ? rerl.list.get(i) : null);
		//					// throw new UnsupportedSyntaxException(loc, "..");
		//				} else if (underlyingFieldType instanceof CStruct) {
		//					final ExpressionListRecResult fieldRerl =
		//							i < rerl.list.size() ? rerl.list.get(i) : new ExpressionListRecResult();
		//					fieldWrites =
		//							initStructOnHeapFromRERL(main, loc, fieldPointer, fieldRerl, (CStruct) underlyingFieldType);
		//
		//				} else if (underlyingFieldType instanceof CNamed) {
		//					throw new AssertionError("This should not be the case as we took the underlying type.");
		//				} else {
		//					throw new UnsupportedSyntaxException(loc, "..");
		//				}
		//			}
		//			newStmt.addAll(fieldWrites.stmt);
		//			newDecl.addAll(fieldWrites.decl);
		//			newAuxVars.putAll(fieldWrites.auxVars);
		//			newOverappr.addAll(fieldWrites.overappr);
		//		}
		//		final ExpressionResult result = new ExpressionResult(newStmt, new RValue(
		//				MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffset, loc),
		//				structType), newDecl, newAuxVars, newOverappr);
		//		return result;
		//	}
		//
		//	/**
		//	 * Takes a ResultExpressionListRec and a CStruct(type) and generates a StructConstructor with the nesting structure
		//	 * from the CStruct and the values from the RERL. If the RERL is null, the default initialization (int: 0, Ptr:
		//	 * NULL, ...) is used for each entry.
		//	 */
		//	private ExpressionResult makeStructConstructorFromRERL(final Dispatcher main, final ILocation loc,
		//			final ExpressionListRecResult rerlIn, final CStruct structType) {
		//		ExpressionListRecResult rerl = null;
		//		if (rerlIn == null) {
		//			rerl = new ExpressionListRecResult();
		//		} else {
		//			rerl = rerlIn;
		//		}
		//
		//		if (rerl.lrVal != null) {
		//			return new ExpressionResult(rerl.stmt, rerl.lrVal, rerl.decl, rerl.auxVars, rerl.overappr);
		//		}
		//
		//		final boolean isUnion = structType instanceof CUnion;
		//		// in a union, only one field of the underlying struct may be initialized
		//		// we do the first, if no fieldname is given, this variable stores whether
		//		// we already initialized a field
		//		boolean unionAlreadyInitialized = false;
		//
		//		// everything for the new Result
		//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
		//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
		//
		//		final String[] fieldIds = structType.getFieldIds();
		//		final CType[] fieldTypes = structType.getFieldTypes();
		//
		//		// the new Arrays for the StructConstructor
		//		final ArrayList<String> fieldIdentifiers = new ArrayList<String>();
		//		final ArrayList<Expression> fieldValues = new ArrayList<Expression>();
		//
		//		for (int i = 0; i < fieldIds.length; i++) {
		//			fieldIdentifiers.add(fieldIds[i]);
		//
		//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
		//
		//			ExpressionResult fieldContents = null;
		//
		//			if (isUnion) {
		//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
		//				// TODO: maybe not use auxiliary variables so lavishly
		//				final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
		//				if (!unionAlreadyInitialized && rerl.list.size() == 1
		//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
		//								|| fieldIds[i].equals(rerl.list.get(0).field))
		//						&& (underlyingFieldType instanceof CStruct
		//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
		//					// use the value from the rerl to initialize the union
		//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, new VariableLHS(loc, tmpId),
		//							underlyingFieldType, rerl.list.get(0));
		//					fieldContents.lrVal = new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType);
		//					unionAlreadyInitialized = true;
		//				} else {
		//					// fill in the uninitialized aux variable
		//					fieldContents =
		//							new ExpressionResult(new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType));
		//				}
		//				final VariableDeclaration auxVarDec =
		//						new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
		//								new String[] { tmpId }, main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
		//				fieldContents.decl.add(auxVarDec);
		//				fieldContents.auxVars.put(auxVarDec, loc);
		//			} else {
		//				if (underlyingFieldType instanceof CPrimitive) {
		//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
		//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
		//				} else if (underlyingFieldType instanceof CPointer) {
		//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
		//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
		//				} else if (underlyingFieldType instanceof CArray) {
		//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
		//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
		//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
		//							new LinkedHashMap<VariableDeclaration, ILocation>();
		//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
		//
		//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, underlyingFieldType);
		//
		//					ExpressionListRecResult arrayInitRerl = null;
		//					if (i < rerl.list.size()) {
		//						arrayInitRerl = rerl.list.get(i);
		//					}
		//
		//					final Expression fieldEx = new IdentifierExpression(loc, tmpId);
		//					final HeapLValue lrVal = new HeapLValue(fieldEx, underlyingFieldType);
		//
		//					final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId,
		//							main.mTypeHandler.cType2AstType(loc, underlyingFieldType), loc);
		//					fieldAuxVars.put(tVarDecl, loc);
		//					fieldDecl.add(tVarDecl);
		//					final VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
		//					final ExpressionResult aInit = main.mCHandler.getInitHandler().initBoogieArray(main, loc,
		//							arrayInitRerl == null ? null : arrayInitRerl.list, fieldLHS, (CArray) underlyingFieldType);
		//
		//					fieldStmt.addAll(aInit.stmt);
		//					fieldDecl.addAll(aInit.decl);
		//					fieldAuxVars.putAll(aInit.auxVars);
		//					fieldOverApp.addAll(aInit.overappr);
		//
		//					fieldContents = new ExpressionResult(fieldStmt, lrVal, fieldDecl, fieldAuxVars, fieldOverApp);
		//				} else if (underlyingFieldType instanceof CEnum) {
		//					// like CPrimitive
		//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
		//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
		//				} else if (underlyingFieldType instanceof CStruct) {
		//					if (i < rerl.list.size()) {
		//						fieldContents = makeStructConstructorFromRERL(main, loc, rerl.list.get(i),
		//								(CStruct) underlyingFieldType);
		//					} else {
		//						fieldContents = makeStructConstructorFromRERL(main, loc, new ExpressionListRecResult(),
		//								(CStruct) underlyingFieldType);
		//					}
		//				} else if (underlyingFieldType instanceof CNamed) {
		//					throw new AssertionError("This should not be the case as we took the underlying type.");
		//				} else {
		//					throw new UnsupportedSyntaxException(loc, "..");
		//				}
		//			}
		//			newStmt.addAll(fieldContents.stmt);
		//			newDecl.addAll(fieldContents.decl);
		//			newAuxVars.putAll(fieldContents.auxVars);
		//			newOverappr.addAll(fieldContents.overappr);
		//			if (fieldContents.lrVal instanceof HeapLValue) {
		//				fieldValues.add(((HeapLValue) fieldContents.lrVal).getAddress());
		//			} else if (fieldContents.lrVal instanceof RValue) {
		//				fieldValues.add(((RValue) fieldContents.lrVal).getValue());
		//			} else {
		//				throw new AssertionError();
		//			}
		//		}
		////		final StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
		//		final StructConstructor sc = new StructConstructor(loc, //new InferredType(Type.Struct),
		//				fieldIdentifiers.toArray(new String[fieldIdentifiers.size()]),
		//				fieldValues.toArray(new Expression[fieldValues.size()]));
		//
		//		final ExpressionResult result =
		//				new ExpressionResult(newStmt, new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
		//		return result;
		//	}
		//
		//	private Expression getDefaultValueForSimpleType(final ILocation loc, final CType cType) {
		//		if (cType instanceof CPrimitive) {
		//			final CPrimitive cPrimitive = (CPrimitive) cType;
		//			switch (cPrimitive.getGeneralType()) {
		//			case INTTYPE:
		//				return mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive,
		//						BigInteger.ZERO);
		//			case FLOATTYPE:
		//				// TODO: which methods in expression translation to use??
		//				//				if (cPrimitive.getType().equals(CPrimitives.FLOAT)) {
		//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
		//				//				} else if (cPrimitive.getType().equals(CPrimitives.DOUBLE)) {
		//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
		//				//				} else if (cPrimitive.getType().equals(CPrimitives.LONGDOUBLE)) {
		//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
		//				//				} else {
		//				//					throw new UnsupportedOperationException("UNsopported Floating Type");
		//				//				}
		//				return mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive,
		//						BigDecimal.ZERO);
		//			case VOID:
		//				throw new AssertionError("cannot initialize something that has type void");
		//			default:
		//				throw new AssertionError("unknown category of type");
		//			}
		//		} else if (cType instanceof CEnum) {
		//			return mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
		//					BigInteger.ZERO);
		//		} else if (cType instanceof CPointer) {
		//			return mExpressionTranslation.constructNullPointer(loc);
		//		} else {
		//			throw new UnsupportedOperationException("missing case?");
		//		}
		//	}
		
		
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

			private static void addOverApprToStatementAnnots(final List<Overapprox> overappr, final Statement stm) {
			for (final Overapprox overapprItem : overappr) {
				overapprItem.annotate(stm);
			}
		}

	//	/**
			//	 * Helper for variable initialization. This version does not take any form of the initialized variable as an
			//	 * argument but instead returns a ResultExpression with an lrValue that can be stored in such a variable.
			//	 */
			//	private ExpressionResult makeVarInitializationNoReturnValue(final ILocation loc, final Dispatcher main,
			//			final CType cType, final ExpressionResult initializerRaw) {
			//		final CType lCType = cType.getUnderlyingType();
			//
			//		final ArrayList<Statement> stmt = new ArrayList<Statement>();
			//		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
			//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			//		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
			//
			//		// if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
			//		// carry over
			//		ExpressionResult initializer = null;
			//		if (initializerRaw != null) {
			//			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			//			stmt.addAll(initializer.stmt);
			//			decl.addAll(initializer.decl);
			//			overappr.addAll(initializer.overappr);
			//			auxVars.putAll(initializer.auxVars);
			//		}
			//
			//		final LRValue lrVal;
			//		final Expression rhs;
			//		if (lCType instanceof CPrimitive) {
			//			if (initializer == null) {
			//				final CPrimitive lCPrimitive = (CPrimitive) lCType;
			//				switch (lCPrimitive.getGeneralType()) {
			//				case INTTYPE:
			//					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, lCPrimitive, BigInteger.ZERO);
			//					break;
			//				case FLOATTYPE:
			//					rhs = mExpressionTranslation.constructLiteralForFloatingType(loc, lCPrimitive, BigDecimal.ONE);
			//					break;
			//				case VOID:
			//					throw new AssertionError("cannot initialize something that has type void");
			//				default:
			//					throw new AssertionError("unknown category of type");
			//				}
			//			} else {
			//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			//				main.mCHandler.convert(loc, initializer, lCType);
			//				rhs = initializer.lrVal.getValue();
			//			}
			//			lrVal = new RValue(rhs, lCType);
			//		} else if (lCType instanceof CPointer) {
			//			if (initializer == null) {
			//				rhs = mExpressionTranslation.constructNullPointer(loc);
			//			} else {
			//				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
			//				if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
			//					rhs = initializer.lrVal.getValue();
			//				} else if (initializerUnderlyingType instanceof CPrimitive
			//						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
			//					final BigInteger pointerOffsetValue =
			//							mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
			//					if (pointerOffsetValue == null) {
			//						throw new IllegalArgumentException("unable to understand " + initializer.lrVal);
			//					}
			//					if (pointerOffsetValue.equals(BigInteger.ZERO)) {
			//						rhs = mExpressionTranslation.constructNullPointer(loc);
			//					} else {
			//						final BigInteger pointerBaseValue = BigInteger.ZERO;
			//						rhs = mExpressionTranslation.constructPointerForIntegerValues(loc, pointerBaseValue,
			//								pointerOffsetValue);
			//					}
			//				} else {
			//					throw new AssertionError(
			//							"trying to initialize a pointer with something different from int and pointer");
			//				}
			//			}
			//
			//			lrVal = new RValue(rhs, lCType);
			//		} else if (lCType instanceof CArray) {
			//			final VariableLHS lhs = null;
			//
			//			if (initializer == null) {
			//				final ExpressionResult aInit = initBoogieArray(main, loc, null, lhs, (CArray) lCType);
			//				stmt.addAll(aInit.stmt);
			//				decl.addAll(aInit.decl);
			//				auxVars.putAll(aInit.auxVars);
			//			} else if (initializer instanceof ExpressionListRecResult) {
			//				final ExpressionResult aInit =
			//						initBoogieArray(main, loc, ((ExpressionListRecResult) initializer).list, lhs, (CArray) lCType);
			//				stmt.addAll(aInit.stmt);
			//				decl.addAll(aInit.decl);
			//				auxVars.putAll(aInit.auxVars);
			//			} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
			//																	// corresponding aux vars
			//				// stmt.addAll(initializer.stmt);
			//				// decl.addAll(initializer.decl);
			//				// auxVars.putAll(initializer.auxVars);
			//			} else {
			//				assert false;
			//			}
			//			// }
			//			assert lhs != null;
			//			lrVal = null;
			//		} else if (lCType instanceof CStruct) {
			//			final CStruct structType = (CStruct) lCType;
			//
			//			final ExpressionResult scRex =
			//					makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
			//
			//			stmt.addAll(scRex.stmt);
			//			decl.addAll(scRex.decl);
			//			overappr.addAll(scRex.overappr);
			//			auxVars.putAll(scRex.auxVars);
			//			rhs = null;
			//			lrVal = new RValue(rhs, lCType);
			//		} else if (lCType instanceof CEnum) {
			//			if (initializer == null) {
			//				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
			//						BigInteger.ZERO);
			//			} else {
			//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			//				rhs = initializer.lrVal.getValue();
			//			}
			//			lrVal = new RValue(rhs, lCType);
			//		} else {
			//			final String msg = "Unknown type - don't know how to initialize!";
			//			throw new UnsupportedSyntaxException(loc, msg);
			//		}
			//		assert CHandler.isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
			//
			//		// lrVal is null in case we got a lhs to assign to, the initializing value otherwise
			//		return new ExpressionResult(stmt, lrVal, decl, auxVars, overappr);
			//	}
			
			//	/**
			//	 * Same as other initVar but with an LRValue as argument, not a LHS if var is a HeapLValue, something on Heap is
			//	 * initialized, if it is a LocalLValue something off the Heap is initialized
			//	 */
			//	private ExpressionResult makeVarInitializationWithGivenReturnValue(final ILocation loc, final Dispatcher main, final LRValue var, final CType cType,
			//			final ExpressionResult initializerRaw) {
			//		assert var != null;
			//
			//		final boolean onHeap = var instanceof HeapLValue;
			//
			//		final CType lCType = cType.getUnderlyingType();
			//
			//		final ArrayList<Statement> stmt = new ArrayList<Statement>();
			//		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
			//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			//		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
			//
			//		// if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
			//		// carry over
			//		ExpressionResult initializer = null;
			//		if (initializerRaw != null) {
			//			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			//			stmt.addAll(initializer.stmt);
			//			decl.addAll(initializer.decl);
			//			overappr.addAll(initializer.overappr);
			//			auxVars.putAll(initializer.auxVars);
			//		}
			//
			//		VariableLHS lhs = null;
			//		if (var instanceof LocalLValue) {
			//			lhs = (VariableLHS) ((LocalLValue) var).getLHS();
			//		}
			//		Expression rhs = null;
			//		if (lCType instanceof CPrimitive) {
			//			switch (((CPrimitive) lCType).getGeneralType()) {
			//			case INTTYPE:
			//				if (initializer == null) {
			//					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, (CPrimitive) lCType,
			//							BigInteger.ZERO);
			//				} else {
			//					initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			//					main.mCHandler.convert(loc, initializer, lCType);
			//					rhs = initializer.lrVal.getValue();
			//				}
			//				break;
			//			case FLOATTYPE:
			//				if (mExpressionTranslation instanceof BitvectorTranslation) {
			//					if (initializer == null) {
			//						if (((CPrimitive) lCType).getType().equals(CPrimitives.FLOAT)) {
			//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
			//						} else if (((CPrimitive) lCType).getType().equals(CPrimitives.DOUBLE)) {
			//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
			//						} else if (((CPrimitive) lCType).getType().equals(CPrimitives.LONGDOUBLE)) {
			//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
			//						} else {
			//							throw new UnsupportedOperationException("UNsopported Floating Type");
			//						}
			//					} else {
			//						main.mCHandler.convert(loc, initializer, lCType);
			//						rhs = initializer.lrVal.getValue();
			//					}
			//				} else {
			//					if (initializer == null) {
			//						rhs = new RealLiteral(loc, SFO.NR0F);
			//					} else {
			//						main.mCHandler.convert(loc, initializer, lCType);
			//						rhs = initializer.lrVal.getValue();
			//					}
			//				}
			//				break;
			//			case VOID:
			//			default:
			//				throw new AssertionError("unknown type to init");
			//			}
			//			if (onHeap) {
			//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, cType));
			//			} else {
			//				assert lhs != null;
			//				final AssignmentStatement assignment =
			//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
			//				addOverApprToStatementAnnots(overappr, assignment);
			//				stmt.add(assignment);
			//			}
			//		} else if (lCType instanceof CPointer) {
			//			if (initializer == null) {
			//				rhs = mExpressionTranslation.constructNullPointer(loc);
			//			} else {
			//				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
			//				if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
			//					rhs = initializer.lrVal.getValue();
			//				} else if (initializerUnderlyingType instanceof CPrimitive
			//						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
			//					final BigInteger offsetValue =
			//							mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
			//					if (offsetValue.equals(BigInteger.ZERO)) {
			//						rhs = mExpressionTranslation.constructNullPointer(loc);
			//					} else {
			//						final Expression base = mExpressionTranslation.constructLiteralForIntegerType(loc,
			//								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
			//						final Expression offset = mExpressionTranslation.constructLiteralForIntegerType(loc,
			//								mExpressionTranslation.getCTypeOfPointerComponents(), offsetValue);
			//						rhs = MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
			//					}
			//				} else {
			//					throw new AssertionError(
			//							"trying to initialize a pointer with something different from int and pointer");
			//				}
			//			}
			//			if (onHeap) {
			//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, lCType));
			//			} else {
			//				assert lhs != null;
			//				final AssignmentStatement assignment =
			//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
			//				addOverApprToStatementAnnots(overappr, assignment);
			//				stmt.add(assignment);
			//			}
			//		} else if (lCType instanceof CArray) {
			//
			//			if (onHeap) {
			//				final IdentifierExpression arrayAddress = (IdentifierExpression) ((HeapLValue) var).getAddress();
			//				lhs = new VariableLHS(arrayAddress.getLocation(), arrayAddress.getIdentifier());
			//
			//				// done in simpleDec
			//				// CallStatement mallocRex = mMemoryHandler.getMallocCall(main, mFunctionHandler,
			//				// mMemoryHandler.calculateSizeOf(lCType, loc), new LocalLValue(lhs, cType), loc);
			//				// stmt.add(mallocRex);
			//
			//				if (initializer == null) {
			//					final ExpressionResult aInit = initArrayOnHeap(main, loc, null, arrayAddress, (CArray) lCType);
			//					stmt.addAll(aInit.stmt);
			//					decl.addAll(aInit.decl);
			//					auxVars.putAll(aInit.auxVars);
			//				} else if (initializer instanceof ExpressionListRecResult) {
			//					final ExpressionResult aInit = initArrayOnHeap(main, loc,
			//							((ExpressionListRecResult) initializer).list, arrayAddress, (CArray) lCType);
			//					stmt.addAll(aInit.stmt);
			//					decl.addAll(aInit.decl);
			//					auxVars.putAll(aInit.auxVars);
			//				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
			//																		// corresponding aux vars
			//					// stmt.addAll(initializer.stmt);
			//					// decl.addAll(initializer.decl);
			//					// auxVars.putAll(initializer.auxVars);
			//				} else {
			//					assert false;
			//				}
			//
			//			} else { // not on Heap
			//				ExpressionResult initRex = null;
			//				if (initializer == null) {
			//					initRex = initBoogieArray(main, loc, null, lhs, (CArray) lCType);
			//				} else if (initializer instanceof ExpressionListRecResult) {
			//					initRex = initBoogieArray(main, loc, ((ExpressionListRecResult) initializer).list, lhs,
			//							(CArray) lCType);
			//				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
			//																		// corresponding aux vars
			//					// stmt.addAll(initializer.stmt);
			//					// decl.addAll(initializer.decl);
			//					// auxVars.putAll(initializer.auxVars);
			//				} else {
			//					assert false;
			//				}
			//				if (initRex != null) {
			//					stmt.addAll(initRex.stmt);
			//					decl.addAll(initRex.decl);
			//					auxVars.putAll(initRex.auxVars);
			//				}
			//			}
			//			assert lhs != null;
			//		} else if (lCType instanceof CStruct) {
			//			final CStruct structType = (CStruct) lCType;
			//
			//			if (onHeap) {
			//				assert var != null;
			//				final ExpressionResult heapWrites = initStructOnHeapFromRERL(main, loc, ((HeapLValue) var).getAddress(),
			//						(ExpressionListRecResult) initializer, structType);
			//
			//				stmt.addAll(heapWrites.stmt);
			//				decl.addAll(heapWrites.decl);
			//				overappr.addAll(heapWrites.overappr);
			//				auxVars.putAll(heapWrites.auxVars);
			//			} else {
			//				final ExpressionResult scRex =
			//						makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
			//
			//				stmt.addAll(scRex.stmt);
			//				decl.addAll(scRex.decl);
			//				overappr.addAll(scRex.overappr);
			//				auxVars.putAll(scRex.auxVars);
			//
			//				assert lhs != null;
			//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
			//						new Expression[] { scRex.lrVal.getValue() });
			//				addOverApprToStatementAnnots(overappr, assignment);
			//				stmt.add(assignment);
			//			}
			//		} else if (lCType instanceof CEnum) {
			//			if (initializer == null) {
			//				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc,
			//						new CPrimitive(CPrimitive.CPrimitives.INT), BigInteger.ZERO);
			//			} else {
			//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			//				rhs = initializer.lrVal.getValue();
			//			}
			//			if (onHeap) {
			//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, cType));
			//			} else {
			//				assert lhs != null;
			//				final Statement assignment =
			//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
			//				addOverApprToStatementAnnots(overappr, assignment);
			//				stmt.add(assignment);
			//			}
			//		} else {
			//			final String msg = "Unknown type - don't know how to initialize!";
			//			throw new UnsupportedSyntaxException(loc, msg);
			//		}
			//		// assert (CHandler.isAuxVarMapcomplete(main, decl, auxVars));
			//
			//		return new ExpressionResult(stmt, null, decl, auxVars, overappr);
			//	}
			
				//	/**
				//	 * Initializes an array that lies on heap, either with some given values or to its default values.
				//	 *
				//	 * @param list
				//	 *            The values that the array should be initialized with, null for default init
				//	 * @param startAddress
				//	 *            The address on the heap that the array starts at
				//	 * @param arrayType
				//	 *            The type of the array (containing its size and value type)
				//	 * @return a list of statements that do the initialization
				//	 */
				//	private ExpressionResult initArrayOnHeap(final Dispatcher main, final ILocation loc,
				//			final List<ExpressionListRecResult> list, final Expression startAddress, final CArray arrayType) {
				//		final List<Statement> stmt = new ArrayList<>();
				//		final List<Declaration> decl = new ArrayList<>();
				//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
				//		final List<Overapprox> overApp = new ArrayList<>();
				//
				//		final Expression sizeOfCell = mMemoryHandler.calculateSizeOf(loc, arrayType.getValueType());
				//		final RValue[] dimensions = arrayType.getDimensions();
				//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
				//		if (dimBigInteger == null) {
				//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
				//		}
				//		final int currentSizeInt = dimBigInteger.intValue();
				//
				//		Expression newStartAddressBase = null;
				//		Expression newStartAddressOffset = null;
				//		if (startAddress instanceof StructConstructor) {
				//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
				//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
				//		} else {
				//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
				//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
				//		}
				//
				//		if (dimensions.length == 1) {
				//			// RValue val = null;
				//
				//			for (int i = 0; i < currentSizeInt; i++) {
				//				CType valueType = arrayType.getValueType().getUnderlyingType();
				//				if (valueType instanceof CEnum) {
				//					valueType = new CPrimitive(CPrimitives.INT);
				//				}
				//
				//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
				//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
				//				Expression writeOffset =
				//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), sizeOfCell,
				//								mExpressionTranslation.getCTypeOfPointerComponents());
				//
				//				writeOffset = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				//						newStartAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(), writeOffset,
				//						mExpressionTranslation.getCTypeOfPointerComponents());
				//
				//				final Expression writeLocation =
				//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, writeOffset, loc);
				//
				//				// TODO: we may need to pass statements, decls, ...
				//				if (list != null && list.size() > i && list.get(i).getLrVal() != null) {
				//					final RValue val = (RValue) list.get(i).getLrVal();
				//					decl.addAll(list.get(i).getDeclarations());
				//					auxVars.putAll(list.get(i).getAuxVars());
				//					stmt.addAll(list.get(i).getStatements());
				//					overApp.addAll(list.get(i).getOverapprs());
				//					stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
				//							val.getValue(), val.getCType()));
				//				} else {
				//					if (valueType instanceof CArray) {
				//						throw new AssertionError(
				//								"this should not be the case as we are in the inner/outermost array right??");
				//					} else if (valueType instanceof CStruct) {
				//						final ExpressionResult sInit = initStructOnHeapFromRERL(main, loc, writeLocation,
				//								list != null && list.size() > i ? list.get(i) : null, (CStruct) valueType);
				//						stmt.addAll(sInit.stmt);
				//						decl.addAll(sInit.decl);
				//						auxVars.putAll(sInit.auxVars);
				//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer) {
				//						final ExpressionResult pInit =
				//								main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType, null);
				//						assert pInit.stmt.isEmpty() && pInit.decl.isEmpty() && pInit.auxVars.isEmpty();
				//						final RValue val = (RValue) pInit.lrVal;
				//						stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
				//								val.getValue(), val.getCType()));
				//					} else {
				//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
				//					}
				//				}
				//			}
				//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
				//		} else {
				//			for (int i = 0; i < currentSizeInt; i++) {
				//				Expression newStartAddressOffsetInner = newStartAddressOffset;
				//
				//				Expression blockOffset = sizeOfCell;
				//				for (int j = 1; j < dimensions.length; j++) {
				//					blockOffset =
				//							mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				//									dimensions[j].getValue(), (CPrimitive) dimensions[j].getCType(), blockOffset,
				//									mExpressionTranslation.getCTypeOfPointerComponents());
				//				}
				//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
				//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
				//				blockOffset =
				//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), blockOffset,
				//								mExpressionTranslation.getCTypeOfPointerComponents());
				//
				//				newStartAddressOffsetInner =
				//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				//								newStartAddressOffsetInner, mExpressionTranslation.getCTypeOfPointerComponents(),
				//								blockOffset, mExpressionTranslation.getCTypeOfPointerComponents());
				//
				//				final ArrayList<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
				//				innerDims.remove(0);// TODO ??
				//				final CArray innerArrayType =
				//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
				//
				//				final ExpressionResult initRex = initArrayOnHeap(main, loc, list != null ? list.get(i).list : null,
				//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffsetInner,
				//								loc),
				//						innerArrayType);
				//				stmt.addAll(initRex.stmt);
				//				decl.addAll(initRex.decl);
				//				auxVars.putAll(initRex.auxVars);
				//				overApp.addAll(initRex.overappr);
				//			}
				//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
				//		}
				//	}
				
				//	/**
				//	 * Initializes an array that is represented as a boogie array, either with some given values or to its default
				//	 * values.
				//	 *
				//	 * @param list
				//	 *            The values that the array should be initialized with, null for default init
				//	 * @param innerArrayAccessLHS
				//	 *            Something representing the array that is to be initialized currently (in case of a nested array this
				//	 *            may again represent an arrayAccess, otherwise the array identifier)
				//	 * @param arrayType
				//	 *            The type of the array (containing its size and value type)
				//	 * @return a list of statements that do the initialization
				//	 */
				//	private ExpressionResult initBoogieArray(final Dispatcher main, final ILocation loc,
				//			final List<ExpressionListRecResult> list, final LeftHandSide innerArrayAccessLHS, final CArray arrayType) {
				//		final List<Statement> stmt = new ArrayList<Statement>();
				//		final List<Declaration> decl = new ArrayList<>();
				//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
				//		final List<Overapprox> overApp = new ArrayList<>();
				//
				//		final RValue[] dimensions = arrayType.getDimensions();
				//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
				//		if (dimBigInteger == null) {
				//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
				//		}
				//		final int currentSizeInt = dimBigInteger.intValue();
				//
				//		if (dimensions.length == 1) {
				//			RValue val = null;
				//
				//			for (int i = 0; i < currentSizeInt; i++) {
				//				if (list != null && list.size() > i && list.get(i).lrVal != null) {
				//					// we have a value to initialize with
				//					final CType valueType = arrayType.getValueType().getUnderlyingType();
				//					main.mCHandler.convert(loc, list.get(i), valueType);
				//					val = (RValue) list.get(i).lrVal;
				//					decl.addAll(list.get(i).decl);
				//					auxVars.putAll(list.get(i).auxVars);
				//					stmt.addAll(list.get(i).stmt);
				//					overApp.addAll(list.get(i).overappr);
				//				} else {
				//					// do default initialization
				//					final CType valueType = arrayType.getValueType().getUnderlyingType();
				//
				//					if (valueType instanceof CArray) {
				//						throw new AssertionError(
				//								"this should not be the case as we are in the inner/outermost array right??");
				//					} else if (valueType instanceof CStruct) {
				//						final ExpressionResult sInit =
				//								makeStructConstructorFromRERL(main, loc, null, (CStruct) valueType);
				//						stmt.addAll(sInit.stmt);
				//						decl.addAll(sInit.decl);
				//						auxVars.putAll(sInit.auxVars);
				//						overApp.addAll(sInit.overappr);
				//						val = (RValue) sInit.lrVal;
				//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer
				//							|| valueType instanceof CEnum) {
				//						val = (RValue) main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType,
				//								null).lrVal;
				//					} else {
				//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
				//					}
				//				}
				//				Expression[] newIndices = null;
				//				LeftHandSide newLHS = null;
				//				final CPrimitive indexType = (CPrimitive) dimensions[0].getCType();
				//				final Expression index =
				//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
				//				if (innerArrayAccessLHS instanceof ArrayLHS) {
				//					final ArrayList<Expression> innerIndices =
				//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
				//					innerIndices.add(index);
				//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
				//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
				//				} else {
				//					newIndices = new Expression[] { index };
				//					newLHS = innerArrayAccessLHS;
				//				}
				//
				//				final ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
				//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { arrayAccessLHS },
				//						new Expression[] { val.getValue() });
				//				addOverApprToStatementAnnots(overApp, assignment);
				//				stmt.add(assignment);
				//			}
				//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
				//		} else {
				//			for (int i = 0; i < currentSizeInt; i++) {
				//
				//				Expression[] newIndices = null;
				//				LeftHandSide newLHS = null;
				//
				//				// 2015-10-24 Matthias: I don't understand where I can take the
				//				// type of the index from. As a workaround I take signed int.
				//				final CPrimitive indexType = new CPrimitive(CPrimitives.INT);
				//				final Expression index =
				//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
				//				if (innerArrayAccessLHS instanceof ArrayLHS) {
				//					final ArrayList<Expression> innerIndices =
				//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
				//					innerIndices.add(index);
				//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
				//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
				//				} else {
				//					newIndices = new Expression[] { index };
				//					newLHS = innerArrayAccessLHS;
				//				}
				//
				//				final List<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
				//				innerDims.remove(0);// TODO ??
				//				final CArray innerArrayType =
				//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
				//
				//				final List<ExpressionListRecResult> listRecCall;
				//				if (list == null) {
				//					listRecCall = null;
				//				} else if (list.size() - 1 < i) {
				//					listRecCall = null;
				//				} else {
				//					listRecCall = list.get(i).list;
				//				}
				//				final ExpressionResult initRex =
				//						initBoogieArray(main, loc, listRecCall, new ArrayLHS(loc, newLHS, newIndices), innerArrayType);
				//				stmt.addAll(initRex.stmt);
				//				decl.addAll(initRex.decl);
				//				auxVars.putAll(initRex.auxVars);
				//				overApp.addAll(initRex.overappr);
				//			}
				//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
				//		}
				//		// return arrayWrites;
				//	}
				//
				//	/**
				//	 * Generate the write calls for the initialization of the struct onHeap.
				//	 */
				//	private ExpressionResult initStructOnHeapFromRERL(final Dispatcher main, final ILocation loc,
				//			final Expression startAddress, final ExpressionListRecResult rerlIn, final CStruct structType) {
				//		ExpressionListRecResult rerl = null;
				//		if (rerlIn == null) {
				//			rerl = new ExpressionListRecResult();
				//		} else {
				//			rerl = rerlIn;
				//		}
				//
				//		if (rerl.lrVal != null) {// we have an identifier (or sth else too?)
				//			final ExpressionResult writes = new ExpressionResult((RValue) null);
				//			final ArrayList<Statement> writeCalls =
				//					mMemoryHandler.getWriteCall(loc, new HeapLValue(startAddress, rerl.lrVal.getCType()),
				//							((RValue) rerl.lrVal).getValue(), rerl.lrVal.getCType());
				//			writes.stmt.addAll(writeCalls);
				//			return writes;
				//		}
				//
				//		Expression newStartAddressBase = null;
				//		Expression newStartAddressOffset = null;
				//		if (startAddress instanceof StructConstructor) {
				//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
				//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
				//		} else {
				//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
				//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
				//		}
				//
				//		// everything for the new Result
				//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
				//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
				//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
				//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
				//
				//		final String[] fieldIds = structType.getFieldIds();
				//		final CType[] fieldTypes = structType.getFieldTypes();
				//
				//		final boolean isUnion = structType instanceof CUnion;
				//		// in a union, only one field of the underlying struct may be initialized
				//		// we do the first, if no fieldname is given, this variable stores whether
				//		// we already initialized a field
				//		boolean unionAlreadyInitialized = false;
				//
				//		for (int i = 0; i < fieldIds.length; i++) {
				//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
				//
				//			final Expression fieldAddressBase = newStartAddressBase;
				//			final Expression fieldAddressOffset =
				//					mStructHandler.computeStructFieldOffset(mMemoryHandler, loc, i, newStartAddressOffset, structType);
				//			final StructConstructor fieldPointer =
				//					MemoryHandler.constructPointerFromBaseAndOffset(fieldAddressBase, fieldAddressOffset, loc);
				//			final HeapLValue fieldHlv = new HeapLValue(fieldPointer, underlyingFieldType);
				//
				//			ExpressionResult fieldWrites = null;
				//
				//			if (isUnion) {
				//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
				//				// TODO: maybe not use auxiliary variables so lavishly
				//				if (!unionAlreadyInitialized && rerl.list.size() == 1
				//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
				//								|| fieldIds[i].equals(rerl.list.get(0).field))
				//						&& (underlyingFieldType instanceof CStruct
				//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
				//					// use the value from the rerl to initialize the union
				//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
				//							rerl.list.get(0));
				//					unionAlreadyInitialized = true;
				//				} else {
				//					// fill in the uninitialized aux variable
				//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
				//
				//					fieldWrites = new ExpressionResult((RValue) null);
				//					fieldWrites.stmt.addAll(mMemoryHandler.getWriteCall(loc, fieldHlv,
				//							new IdentifierExpression(loc, tmpId), underlyingFieldType));
				//					final VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0],
				//							new VarList[] { new VarList(loc, new String[] { tmpId },
				//									main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
				//					fieldWrites.decl.add(auxVarDec);
				//					fieldWrites.auxVars.put(auxVarDec, loc);
				//				}
				//
				//			} else {
				//				if (underlyingFieldType instanceof CPrimitive) {
				//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
				//							i < rerl.list.size() ? rerl.list.get(i) : null);
				//				} else if (underlyingFieldType instanceof CPointer) {
				//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
				//							i < rerl.list.size() ? rerl.list.get(i) : null);
				//				} else if (underlyingFieldType instanceof CArray) {
				//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
				//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
				//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
				//							new LinkedHashMap<VariableDeclaration, ILocation>();
				//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
				//
				//					ExpressionListRecResult arrayInitRerl = null;
				//					if (i < rerl.list.size()) {
				//						arrayInitRerl = rerl.list.get(i);
				//					}
				//
				//					final ExpressionResult aInit =
				//							initArrayOnHeap(main, loc, arrayInitRerl == null ? null : arrayInitRerl.list, fieldPointer,
				//									(CArray) underlyingFieldType);
				//					fieldStmt.addAll(aInit.stmt);
				//					fieldDecl.addAll(aInit.decl);
				//					fieldAuxVars.putAll(aInit.auxVars);
				//					fieldOverApp.addAll(aInit.overappr);
				//
				//					fieldWrites = new ExpressionResult(fieldStmt, null, fieldDecl, fieldAuxVars, fieldOverApp);
				//				} else if (underlyingFieldType instanceof CEnum) {
				//					// like CPrimitive (?)
				//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
				//							i < rerl.list.size() ? rerl.list.get(i) : null);
				//					// throw new UnsupportedSyntaxException(loc, "..");
				//				} else if (underlyingFieldType instanceof CStruct) {
				//					final ExpressionListRecResult fieldRerl =
				//							i < rerl.list.size() ? rerl.list.get(i) : new ExpressionListRecResult();
				//					fieldWrites =
				//							initStructOnHeapFromRERL(main, loc, fieldPointer, fieldRerl, (CStruct) underlyingFieldType);
				//
				//				} else if (underlyingFieldType instanceof CNamed) {
				//					throw new AssertionError("This should not be the case as we took the underlying type.");
				//				} else {
				//					throw new UnsupportedSyntaxException(loc, "..");
				//				}
				//			}
				//			newStmt.addAll(fieldWrites.stmt);
				//			newDecl.addAll(fieldWrites.decl);
				//			newAuxVars.putAll(fieldWrites.auxVars);
				//			newOverappr.addAll(fieldWrites.overappr);
				//		}
				//		final ExpressionResult result = new ExpressionResult(newStmt, new RValue(
				//				MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffset, loc),
				//				structType), newDecl, newAuxVars, newOverappr);
				//		return result;
				//	}
				//
				//	/**
				//	 * Takes a ResultExpressionListRec and a CStruct(type) and generates a StructConstructor with the nesting structure
				//	 * from the CStruct and the values from the RERL. If the RERL is null, the default initialization (int: 0, Ptr:
				//	 * NULL, ...) is used for each entry.
				//	 */
				//	private ExpressionResult makeStructConstructorFromRERL(final Dispatcher main, final ILocation loc,
				//			final ExpressionListRecResult rerlIn, final CStruct structType) {
				//		ExpressionListRecResult rerl = null;
				//		if (rerlIn == null) {
				//			rerl = new ExpressionListRecResult();
				//		} else {
				//			rerl = rerlIn;
				//		}
				//
				//		if (rerl.lrVal != null) {
				//			return new ExpressionResult(rerl.stmt, rerl.lrVal, rerl.decl, rerl.auxVars, rerl.overappr);
				//		}
				//
				//		final boolean isUnion = structType instanceof CUnion;
				//		// in a union, only one field of the underlying struct may be initialized
				//		// we do the first, if no fieldname is given, this variable stores whether
				//		// we already initialized a field
				//		boolean unionAlreadyInitialized = false;
				//
				//		// everything for the new Result
				//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
				//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
				//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
				//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
				//
				//		final String[] fieldIds = structType.getFieldIds();
				//		final CType[] fieldTypes = structType.getFieldTypes();
				//
				//		// the new Arrays for the StructConstructor
				//		final ArrayList<String> fieldIdentifiers = new ArrayList<String>();
				//		final ArrayList<Expression> fieldValues = new ArrayList<Expression>();
				//
				//		for (int i = 0; i < fieldIds.length; i++) {
				//			fieldIdentifiers.add(fieldIds[i]);
				//
				//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
				//
				//			ExpressionResult fieldContents = null;
				//
				//			if (isUnion) {
				//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
				//				// TODO: maybe not use auxiliary variables so lavishly
				//				final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
				//				if (!unionAlreadyInitialized && rerl.list.size() == 1
				//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
				//								|| fieldIds[i].equals(rerl.list.get(0).field))
				//						&& (underlyingFieldType instanceof CStruct
				//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
				//					// use the value from the rerl to initialize the union
				//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, new VariableLHS(loc, tmpId),
				//							underlyingFieldType, rerl.list.get(0));
				//					fieldContents.lrVal = new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType);
				//					unionAlreadyInitialized = true;
				//				} else {
				//					// fill in the uninitialized aux variable
				//					fieldContents =
				//							new ExpressionResult(new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType));
				//				}
				//				final VariableDeclaration auxVarDec =
				//						new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
				//								new String[] { tmpId }, main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
				//				fieldContents.decl.add(auxVarDec);
				//				fieldContents.auxVars.put(auxVarDec, loc);
				//			} else {
				//				if (underlyingFieldType instanceof CPrimitive) {
				//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
				//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
				//				} else if (underlyingFieldType instanceof CPointer) {
				//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
				//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
				//				} else if (underlyingFieldType instanceof CArray) {
				//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
				//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
				//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
				//							new LinkedHashMap<VariableDeclaration, ILocation>();
				//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
				//
				//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, underlyingFieldType);
				//
				//					ExpressionListRecResult arrayInitRerl = null;
				//					if (i < rerl.list.size()) {
				//						arrayInitRerl = rerl.list.get(i);
				//					}
				//
				//					final Expression fieldEx = new IdentifierExpression(loc, tmpId);
				//					final HeapLValue lrVal = new HeapLValue(fieldEx, underlyingFieldType);
				//
				//					final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId,
				//							main.mTypeHandler.cType2AstType(loc, underlyingFieldType), loc);
				//					fieldAuxVars.put(tVarDecl, loc);
				//					fieldDecl.add(tVarDecl);
				//					final VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
				//					final ExpressionResult aInit = main.mCHandler.getInitHandler().initBoogieArray(main, loc,
				//							arrayInitRerl == null ? null : arrayInitRerl.list, fieldLHS, (CArray) underlyingFieldType);
				//
				//					fieldStmt.addAll(aInit.stmt);
				//					fieldDecl.addAll(aInit.decl);
				//					fieldAuxVars.putAll(aInit.auxVars);
				//					fieldOverApp.addAll(aInit.overappr);
				//
				//					fieldContents = new ExpressionResult(fieldStmt, lrVal, fieldDecl, fieldAuxVars, fieldOverApp);
				//				} else if (underlyingFieldType instanceof CEnum) {
				//					// like CPrimitive
				//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
				//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
				//				} else if (underlyingFieldType instanceof CStruct) {
				//					if (i < rerl.list.size()) {
				//						fieldContents = makeStructConstructorFromRERL(main, loc, rerl.list.get(i),
				//								(CStruct) underlyingFieldType);
				//					} else {
				//						fieldContents = makeStructConstructorFromRERL(main, loc, new ExpressionListRecResult(),
				//								(CStruct) underlyingFieldType);
				//					}
				//				} else if (underlyingFieldType instanceof CNamed) {
				//					throw new AssertionError("This should not be the case as we took the underlying type.");
				//				} else {
				//					throw new UnsupportedSyntaxException(loc, "..");
				//				}
				//			}
				//			newStmt.addAll(fieldContents.stmt);
				//			newDecl.addAll(fieldContents.decl);
				//			newAuxVars.putAll(fieldContents.auxVars);
				//			newOverappr.addAll(fieldContents.overappr);
				//			if (fieldContents.lrVal instanceof HeapLValue) {
				//				fieldValues.add(((HeapLValue) fieldContents.lrVal).getAddress());
				//			} else if (fieldContents.lrVal instanceof RValue) {
				//				fieldValues.add(((RValue) fieldContents.lrVal).getValue());
				//			} else {
				//				throw new AssertionError();
				//			}
				//		}
				////		final StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
				//		final StructConstructor sc = new StructConstructor(loc, //new InferredType(Type.Struct),
				//				fieldIdentifiers.toArray(new String[fieldIdentifiers.size()]),
				//				fieldValues.toArray(new Expression[fieldValues.size()]));
				//
				//		final ExpressionResult result =
				//				new ExpressionResult(newStmt, new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
				//		return result;
				//	}
				//
				//	private Expression getDefaultValueForSimpleType(final ILocation loc, final CType cType) {
				//		if (cType instanceof CPrimitive) {
				//			final CPrimitive cPrimitive = (CPrimitive) cType;
				//			switch (cPrimitive.getGeneralType()) {
				//			case INTTYPE:
				//				return mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive,
				//						BigInteger.ZERO);
				//			case FLOATTYPE:
				//				// TODO: which methods in expression translation to use??
				//				//				if (cPrimitive.getType().equals(CPrimitives.FLOAT)) {
				//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
				//				//				} else if (cPrimitive.getType().equals(CPrimitives.DOUBLE)) {
				//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
				//				//				} else if (cPrimitive.getType().equals(CPrimitives.LONGDOUBLE)) {
				//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
				//				//				} else {
				//				//					throw new UnsupportedOperationException("UNsopported Floating Type");
				//				//				}
				//				return mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive,
				//						BigDecimal.ZERO);
				//			case VOID:
				//				throw new AssertionError("cannot initialize something that has type void");
				//			default:
				//				throw new AssertionError("unknown category of type");
				//			}
				//		} else if (cType instanceof CEnum) {
				//			return mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
				//					BigInteger.ZERO);
				//		} else if (cType instanceof CPointer) {
				//			return mExpressionTranslation.constructNullPointer(loc);
				//		} else {
				//			throw new UnsupportedOperationException("missing case?");
				//		}
				//	}
				
				
					public List<Declaration> declareInitializationInfrastructure(final Dispatcher main, final ILocation loc) {
						return Collections.emptyList();
					}

//	/**
//	 * Helper for variable initialization. This version does not take any form of the initialized variable as an
//	 * argument but instead returns a ResultExpression with an lrValue that can be stored in such a variable.
//	 */
//	private ExpressionResult makeVarInitializationNoReturnValue(final ILocation loc, final Dispatcher main,
//			final CType cType, final ExpressionResult initializerRaw) {
//		final CType lCType = cType.getUnderlyingType();
//
//		final ArrayList<Statement> stmt = new ArrayList<Statement>();
//		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
//		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
//
//		// if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
//		// carry over
//		ExpressionResult initializer = null;
//		if (initializerRaw != null) {
//			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
//			stmt.addAll(initializer.stmt);
//			decl.addAll(initializer.decl);
//			overappr.addAll(initializer.overappr);
//			auxVars.putAll(initializer.auxVars);
//		}
//
//		final LRValue lrVal;
//		final Expression rhs;
//		if (lCType instanceof CPrimitive) {
//			if (initializer == null) {
//				final CPrimitive lCPrimitive = (CPrimitive) lCType;
//				switch (lCPrimitive.getGeneralType()) {
//				case INTTYPE:
//					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, lCPrimitive, BigInteger.ZERO);
//					break;
//				case FLOATTYPE:
//					rhs = mExpressionTranslation.constructLiteralForFloatingType(loc, lCPrimitive, BigDecimal.ONE);
//					break;
//				case VOID:
//					throw new AssertionError("cannot initialize something that has type void");
//				default:
//					throw new AssertionError("unknown category of type");
//				}
//			} else {
//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
//				main.mCHandler.convert(loc, initializer, lCType);
//				rhs = initializer.lrVal.getValue();
//			}
//			lrVal = new RValue(rhs, lCType);
//		} else if (lCType instanceof CPointer) {
//			if (initializer == null) {
//				rhs = mExpressionTranslation.constructNullPointer(loc);
//			} else {
//				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
//				if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
//					rhs = initializer.lrVal.getValue();
//				} else if (initializerUnderlyingType instanceof CPrimitive
//						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
//					final BigInteger pointerOffsetValue =
//							mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
//					if (pointerOffsetValue == null) {
//						throw new IllegalArgumentException("unable to understand " + initializer.lrVal);
//					}
//					if (pointerOffsetValue.equals(BigInteger.ZERO)) {
//						rhs = mExpressionTranslation.constructNullPointer(loc);
//					} else {
//						final BigInteger pointerBaseValue = BigInteger.ZERO;
//						rhs = mExpressionTranslation.constructPointerForIntegerValues(loc, pointerBaseValue,
//								pointerOffsetValue);
//					}
//				} else {
//					throw new AssertionError(
//							"trying to initialize a pointer with something different from int and pointer");
//				}
//			}
//
//			lrVal = new RValue(rhs, lCType);
//		} else if (lCType instanceof CArray) {
//			final VariableLHS lhs = null;
//
//			if (initializer == null) {
//				final ExpressionResult aInit = initBoogieArray(main, loc, null, lhs, (CArray) lCType);
//				stmt.addAll(aInit.stmt);
//				decl.addAll(aInit.decl);
//				auxVars.putAll(aInit.auxVars);
//			} else if (initializer instanceof ExpressionListRecResult) {
//				final ExpressionResult aInit =
//						initBoogieArray(main, loc, ((ExpressionListRecResult) initializer).list, lhs, (CArray) lCType);
//				stmt.addAll(aInit.stmt);
//				decl.addAll(aInit.decl);
//				auxVars.putAll(aInit.auxVars);
//			} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
//																	// corresponding aux vars
//				// stmt.addAll(initializer.stmt);
//				// decl.addAll(initializer.decl);
//				// auxVars.putAll(initializer.auxVars);
//			} else {
//				assert false;
//			}
//			// }
//			assert lhs != null;
//			lrVal = null;
//		} else if (lCType instanceof CStruct) {
//			final CStruct structType = (CStruct) lCType;
//
//			final ExpressionResult scRex =
//					makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
//
//			stmt.addAll(scRex.stmt);
//			decl.addAll(scRex.decl);
//			overappr.addAll(scRex.overappr);
//			auxVars.putAll(scRex.auxVars);
//			rhs = null;
//			lrVal = new RValue(rhs, lCType);
//		} else if (lCType instanceof CEnum) {
//			if (initializer == null) {
//				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
//						BigInteger.ZERO);
//			} else {
//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
//				rhs = initializer.lrVal.getValue();
//			}
//			lrVal = new RValue(rhs, lCType);
//		} else {
//			final String msg = "Unknown type - don't know how to initialize!";
//			throw new UnsupportedSyntaxException(loc, msg);
//		}
//		assert CHandler.isAuxVarMapcomplete(main.mNameHandler, decl, auxVars);
//
//		// lrVal is null in case we got a lhs to assign to, the initializing value otherwise
//		return new ExpressionResult(stmt, lrVal, decl, auxVars, overappr);
//	}

//	/**
//	 * Same as other initVar but with an LRValue as argument, not a LHS if var is a HeapLValue, something on Heap is
//	 * initialized, if it is a LocalLValue something off the Heap is initialized
//	 */
//	private ExpressionResult makeVarInitializationWithGivenReturnValue(final ILocation loc, final Dispatcher main, final LRValue var, final CType cType,
//			final ExpressionResult initializerRaw) {
//		assert var != null;
//
//		final boolean onHeap = var instanceof HeapLValue;
//
//		final CType lCType = cType.getUnderlyingType();
//
//		final ArrayList<Statement> stmt = new ArrayList<Statement>();
//		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
//		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
//
//		// if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
//		// carry over
//		ExpressionResult initializer = null;
//		if (initializerRaw != null) {
//			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
//			stmt.addAll(initializer.stmt);
//			decl.addAll(initializer.decl);
//			overappr.addAll(initializer.overappr);
//			auxVars.putAll(initializer.auxVars);
//		}
//
//		VariableLHS lhs = null;
//		if (var instanceof LocalLValue) {
//			lhs = (VariableLHS) ((LocalLValue) var).getLHS();
//		}
//		Expression rhs = null;
//		if (lCType instanceof CPrimitive) {
//			switch (((CPrimitive) lCType).getGeneralType()) {
//			case INTTYPE:
//				if (initializer == null) {
//					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, (CPrimitive) lCType,
//							BigInteger.ZERO);
//				} else {
//					initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
//					main.mCHandler.convert(loc, initializer, lCType);
//					rhs = initializer.lrVal.getValue();
//				}
//				break;
//			case FLOATTYPE:
//				if (mExpressionTranslation instanceof BitvectorTranslation) {
//					if (initializer == null) {
//						if (((CPrimitive) lCType).getType().equals(CPrimitives.FLOAT)) {
//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
//						} else if (((CPrimitive) lCType).getType().equals(CPrimitives.DOUBLE)) {
//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
//						} else if (((CPrimitive) lCType).getType().equals(CPrimitives.LONGDOUBLE)) {
//							rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
//						} else {
//							throw new UnsupportedOperationException("UNsopported Floating Type");
//						}
//					} else {
//						main.mCHandler.convert(loc, initializer, lCType);
//						rhs = initializer.lrVal.getValue();
//					}
//				} else {
//					if (initializer == null) {
//						rhs = new RealLiteral(loc, SFO.NR0F);
//					} else {
//						main.mCHandler.convert(loc, initializer, lCType);
//						rhs = initializer.lrVal.getValue();
//					}
//				}
//				break;
//			case VOID:
//			default:
//				throw new AssertionError("unknown type to init");
//			}
//			if (onHeap) {
//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, cType));
//			} else {
//				assert lhs != null;
//				final AssignmentStatement assignment =
//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
//				addOverApprToStatementAnnots(overappr, assignment);
//				stmt.add(assignment);
//			}
//		} else if (lCType instanceof CPointer) {
//			if (initializer == null) {
//				rhs = mExpressionTranslation.constructNullPointer(loc);
//			} else {
//				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
//				if (initializerUnderlyingType instanceof CPointer || initializerUnderlyingType instanceof CArray) {
//					rhs = initializer.lrVal.getValue();
//				} else if (initializerUnderlyingType instanceof CPrimitive
//						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
//					final BigInteger offsetValue =
//							mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
//					if (offsetValue.equals(BigInteger.ZERO)) {
//						rhs = mExpressionTranslation.constructNullPointer(loc);
//					} else {
//						final Expression base = mExpressionTranslation.constructLiteralForIntegerType(loc,
//								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
//						final Expression offset = mExpressionTranslation.constructLiteralForIntegerType(loc,
//								mExpressionTranslation.getCTypeOfPointerComponents(), offsetValue);
//						rhs = MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
//					}
//				} else {
//					throw new AssertionError(
//							"trying to initialize a pointer with something different from int and pointer");
//				}
//			}
//			if (onHeap) {
//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, lCType));
//			} else {
//				assert lhs != null;
//				final AssignmentStatement assignment =
//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
//				addOverApprToStatementAnnots(overappr, assignment);
//				stmt.add(assignment);
//			}
//		} else if (lCType instanceof CArray) {
//
//			if (onHeap) {
//				final IdentifierExpression arrayAddress = (IdentifierExpression) ((HeapLValue) var).getAddress();
//				lhs = new VariableLHS(arrayAddress.getLocation(), arrayAddress.getIdentifier());
//
//				// done in simpleDec
//				// CallStatement mallocRex = mMemoryHandler.getMallocCall(main, mFunctionHandler,
//				// mMemoryHandler.calculateSizeOf(lCType, loc), new LocalLValue(lhs, cType), loc);
//				// stmt.add(mallocRex);
//
//				if (initializer == null) {
//					final ExpressionResult aInit = initArrayOnHeap(main, loc, null, arrayAddress, (CArray) lCType);
//					stmt.addAll(aInit.stmt);
//					decl.addAll(aInit.decl);
//					auxVars.putAll(aInit.auxVars);
//				} else if (initializer instanceof ExpressionListRecResult) {
//					final ExpressionResult aInit = initArrayOnHeap(main, loc,
//							((ExpressionListRecResult) initializer).list, arrayAddress, (CArray) lCType);
//					stmt.addAll(aInit.stmt);
//					decl.addAll(aInit.decl);
//					auxVars.putAll(aInit.auxVars);
//				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
//																		// corresponding aux vars
//					// stmt.addAll(initializer.stmt);
//					// decl.addAll(initializer.decl);
//					// auxVars.putAll(initializer.auxVars);
//				} else {
//					assert false;
//				}
//
//			} else { // not on Heap
//				ExpressionResult initRex = null;
//				if (initializer == null) {
//					initRex = initBoogieArray(main, loc, null, lhs, (CArray) lCType);
//				} else if (initializer instanceof ExpressionListRecResult) {
//					initRex = initBoogieArray(main, loc, ((ExpressionListRecResult) initializer).list, lhs,
//							(CArray) lCType);
//				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the
//																		// corresponding aux vars
//					// stmt.addAll(initializer.stmt);
//					// decl.addAll(initializer.decl);
//					// auxVars.putAll(initializer.auxVars);
//				} else {
//					assert false;
//				}
//				if (initRex != null) {
//					stmt.addAll(initRex.stmt);
//					decl.addAll(initRex.decl);
//					auxVars.putAll(initRex.auxVars);
//				}
//			}
//			assert lhs != null;
//		} else if (lCType instanceof CStruct) {
//			final CStruct structType = (CStruct) lCType;
//
//			if (onHeap) {
//				assert var != null;
//				final ExpressionResult heapWrites = initStructOnHeapFromRERL(main, loc, ((HeapLValue) var).getAddress(),
//						(ExpressionListRecResult) initializer, structType);
//
//				stmt.addAll(heapWrites.stmt);
//				decl.addAll(heapWrites.decl);
//				overappr.addAll(heapWrites.overappr);
//				auxVars.putAll(heapWrites.auxVars);
//			} else {
//				final ExpressionResult scRex =
//						makeStructConstructorFromRERL(main, loc, (ExpressionListRecResult) initializer, structType);
//
//				stmt.addAll(scRex.stmt);
//				decl.addAll(scRex.decl);
//				overappr.addAll(scRex.overappr);
//				auxVars.putAll(scRex.auxVars);
//
//				assert lhs != null;
//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
//						new Expression[] { scRex.lrVal.getValue() });
//				addOverApprToStatementAnnots(overappr, assignment);
//				stmt.add(assignment);
//			}
//		} else if (lCType instanceof CEnum) {
//			if (initializer == null) {
//				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc,
//						new CPrimitive(CPrimitive.CPrimitives.INT), BigInteger.ZERO);
//			} else {
//				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
//				rhs = initializer.lrVal.getValue();
//			}
//			if (onHeap) {
//				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, cType));
//			} else {
//				assert lhs != null;
//				final Statement assignment =
//						new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rhs });
//				addOverApprToStatementAnnots(overappr, assignment);
//				stmt.add(assignment);
//			}
//		} else {
//			final String msg = "Unknown type - don't know how to initialize!";
//			throw new UnsupportedSyntaxException(loc, msg);
//		}
//		// assert (CHandler.isAuxVarMapcomplete(main, decl, auxVars));
//
//		return new ExpressionResult(stmt, null, decl, auxVars, overappr);
//	}

	//	/**
	//	 * Initializes an array that lies on heap, either with some given values or to its default values.
	//	 *
	//	 * @param list
	//	 *            The values that the array should be initialized with, null for default init
	//	 * @param startAddress
	//	 *            The address on the heap that the array starts at
	//	 * @param arrayType
	//	 *            The type of the array (containing its size and value type)
	//	 * @return a list of statements that do the initialization
	//	 */
	//	private ExpressionResult initArrayOnHeap(final Dispatcher main, final ILocation loc,
	//			final List<ExpressionListRecResult> list, final Expression startAddress, final CArray arrayType) {
	//		final List<Statement> stmt = new ArrayList<>();
	//		final List<Declaration> decl = new ArrayList<>();
	//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
	//		final List<Overapprox> overApp = new ArrayList<>();
	//
	//		final Expression sizeOfCell = mMemoryHandler.calculateSizeOf(loc, arrayType.getValueType());
	//		final RValue[] dimensions = arrayType.getDimensions();
	//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
	//		if (dimBigInteger == null) {
	//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
	//		}
	//		final int currentSizeInt = dimBigInteger.intValue();
	//
	//		Expression newStartAddressBase = null;
	//		Expression newStartAddressOffset = null;
	//		if (startAddress instanceof StructConstructor) {
	//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
	//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
	//		} else {
	//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
	//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
	//		}
	//
	//		if (dimensions.length == 1) {
	//			// RValue val = null;
	//
	//			for (int i = 0; i < currentSizeInt; i++) {
	//				CType valueType = arrayType.getValueType().getUnderlyingType();
	//				if (valueType instanceof CEnum) {
	//					valueType = new CPrimitive(CPrimitives.INT);
	//				}
	//
	//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
	//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
	//				Expression writeOffset =
	//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
	//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), sizeOfCell,
	//								mExpressionTranslation.getCTypeOfPointerComponents());
	//
	//				writeOffset = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
	//						newStartAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(), writeOffset,
	//						mExpressionTranslation.getCTypeOfPointerComponents());
	//
	//				final Expression writeLocation =
	//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, writeOffset, loc);
	//
	//				// TODO: we may need to pass statements, decls, ...
	//				if (list != null && list.size() > i && list.get(i).getLrVal() != null) {
	//					final RValue val = (RValue) list.get(i).getLrVal();
	//					decl.addAll(list.get(i).getDeclarations());
	//					auxVars.putAll(list.get(i).getAuxVars());
	//					stmt.addAll(list.get(i).getStatements());
	//					overApp.addAll(list.get(i).getOverapprs());
	//					stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
	//							val.getValue(), val.getCType()));
	//				} else {
	//					if (valueType instanceof CArray) {
	//						throw new AssertionError(
	//								"this should not be the case as we are in the inner/outermost array right??");
	//					} else if (valueType instanceof CStruct) {
	//						final ExpressionResult sInit = initStructOnHeapFromRERL(main, loc, writeLocation,
	//								list != null && list.size() > i ? list.get(i) : null, (CStruct) valueType);
	//						stmt.addAll(sInit.stmt);
	//						decl.addAll(sInit.decl);
	//						auxVars.putAll(sInit.auxVars);
	//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer) {
	//						final ExpressionResult pInit =
	//								main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType, null);
	//						assert pInit.stmt.isEmpty() && pInit.decl.isEmpty() && pInit.auxVars.isEmpty();
	//						final RValue val = (RValue) pInit.lrVal;
	//						stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
	//								val.getValue(), val.getCType()));
	//					} else {
	//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
	//					}
	//				}
	//			}
	//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
	//		} else {
	//			for (int i = 0; i < currentSizeInt; i++) {
	//				Expression newStartAddressOffsetInner = newStartAddressOffset;
	//
	//				Expression blockOffset = sizeOfCell;
	//				for (int j = 1; j < dimensions.length; j++) {
	//					blockOffset =
	//							mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
	//									dimensions[j].getValue(), (CPrimitive) dimensions[j].getCType(), blockOffset,
	//									mExpressionTranslation.getCTypeOfPointerComponents());
	//				}
	//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
	//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
	//				blockOffset =
	//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
	//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), blockOffset,
	//								mExpressionTranslation.getCTypeOfPointerComponents());
	//
	//				newStartAddressOffsetInner =
	//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
	//								newStartAddressOffsetInner, mExpressionTranslation.getCTypeOfPointerComponents(),
	//								blockOffset, mExpressionTranslation.getCTypeOfPointerComponents());
	//
	//				final ArrayList<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
	//				innerDims.remove(0);// TODO ??
	//				final CArray innerArrayType =
	//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
	//
	//				final ExpressionResult initRex = initArrayOnHeap(main, loc, list != null ? list.get(i).list : null,
	//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffsetInner,
	//								loc),
	//						innerArrayType);
	//				stmt.addAll(initRex.stmt);
	//				decl.addAll(initRex.decl);
	//				auxVars.putAll(initRex.auxVars);
	//				overApp.addAll(initRex.overappr);
	//			}
	//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
	//		}
	//	}
	
	//	/**
	//	 * Initializes an array that is represented as a boogie array, either with some given values or to its default
	//	 * values.
	//	 *
	//	 * @param list
	//	 *            The values that the array should be initialized with, null for default init
	//	 * @param innerArrayAccessLHS
	//	 *            Something representing the array that is to be initialized currently (in case of a nested array this
	//	 *            may again represent an arrayAccess, otherwise the array identifier)
	//	 * @param arrayType
	//	 *            The type of the array (containing its size and value type)
	//	 * @return a list of statements that do the initialization
	//	 */
	//	private ExpressionResult initBoogieArray(final Dispatcher main, final ILocation loc,
	//			final List<ExpressionListRecResult> list, final LeftHandSide innerArrayAccessLHS, final CArray arrayType) {
	//		final List<Statement> stmt = new ArrayList<Statement>();
	//		final List<Declaration> decl = new ArrayList<>();
	//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
	//		final List<Overapprox> overApp = new ArrayList<>();
	//
	//		final RValue[] dimensions = arrayType.getDimensions();
	//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
	//		if (dimBigInteger == null) {
	//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
	//		}
	//		final int currentSizeInt = dimBigInteger.intValue();
	//
	//		if (dimensions.length == 1) {
	//			RValue val = null;
	//
	//			for (int i = 0; i < currentSizeInt; i++) {
	//				if (list != null && list.size() > i && list.get(i).lrVal != null) {
	//					// we have a value to initialize with
	//					final CType valueType = arrayType.getValueType().getUnderlyingType();
	//					main.mCHandler.convert(loc, list.get(i), valueType);
	//					val = (RValue) list.get(i).lrVal;
	//					decl.addAll(list.get(i).decl);
	//					auxVars.putAll(list.get(i).auxVars);
	//					stmt.addAll(list.get(i).stmt);
	//					overApp.addAll(list.get(i).overappr);
	//				} else {
	//					// do default initialization
	//					final CType valueType = arrayType.getValueType().getUnderlyingType();
	//
	//					if (valueType instanceof CArray) {
	//						throw new AssertionError(
	//								"this should not be the case as we are in the inner/outermost array right??");
	//					} else if (valueType instanceof CStruct) {
	//						final ExpressionResult sInit =
	//								makeStructConstructorFromRERL(main, loc, null, (CStruct) valueType);
	//						stmt.addAll(sInit.stmt);
	//						decl.addAll(sInit.decl);
	//						auxVars.putAll(sInit.auxVars);
	//						overApp.addAll(sInit.overappr);
	//						val = (RValue) sInit.lrVal;
	//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer
	//							|| valueType instanceof CEnum) {
	//						val = (RValue) main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType,
	//								null).lrVal;
	//					} else {
	//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
	//					}
	//				}
	//				Expression[] newIndices = null;
	//				LeftHandSide newLHS = null;
	//				final CPrimitive indexType = (CPrimitive) dimensions[0].getCType();
	//				final Expression index =
	//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
	//				if (innerArrayAccessLHS instanceof ArrayLHS) {
	//					final ArrayList<Expression> innerIndices =
	//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
	//					innerIndices.add(index);
	//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
	//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
	//				} else {
	//					newIndices = new Expression[] { index };
	//					newLHS = innerArrayAccessLHS;
	//				}
	//
	//				final ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
	//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { arrayAccessLHS },
	//						new Expression[] { val.getValue() });
	//				addOverApprToStatementAnnots(overApp, assignment);
	//				stmt.add(assignment);
	//			}
	//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
	//		} else {
	//			for (int i = 0; i < currentSizeInt; i++) {
	//
	//				Expression[] newIndices = null;
	//				LeftHandSide newLHS = null;
	//
	//				// 2015-10-24 Matthias: I don't understand where I can take the
	//				// type of the index from. As a workaround I take signed int.
	//				final CPrimitive indexType = new CPrimitive(CPrimitives.INT);
	//				final Expression index =
	//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
	//				if (innerArrayAccessLHS instanceof ArrayLHS) {
	//					final ArrayList<Expression> innerIndices =
	//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
	//					innerIndices.add(index);
	//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
	//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
	//				} else {
	//					newIndices = new Expression[] { index };
	//					newLHS = innerArrayAccessLHS;
	//				}
	//
	//				final List<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
	//				innerDims.remove(0);// TODO ??
	//				final CArray innerArrayType =
	//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
	//
	//				final List<ExpressionListRecResult> listRecCall;
	//				if (list == null) {
	//					listRecCall = null;
	//				} else if (list.size() - 1 < i) {
	//					listRecCall = null;
	//				} else {
	//					listRecCall = list.get(i).list;
	//				}
	//				final ExpressionResult initRex =
	//						initBoogieArray(main, loc, listRecCall, new ArrayLHS(loc, newLHS, newIndices), innerArrayType);
	//				stmt.addAll(initRex.stmt);
	//				decl.addAll(initRex.decl);
	//				auxVars.putAll(initRex.auxVars);
	//				overApp.addAll(initRex.overappr);
	//			}
	//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
	//		}
	//		// return arrayWrites;
	//	}
	//
	//	/**
	//	 * Generate the write calls for the initialization of the struct onHeap.
	//	 */
	//	private ExpressionResult initStructOnHeapFromRERL(final Dispatcher main, final ILocation loc,
	//			final Expression startAddress, final ExpressionListRecResult rerlIn, final CStruct structType) {
	//		ExpressionListRecResult rerl = null;
	//		if (rerlIn == null) {
	//			rerl = new ExpressionListRecResult();
	//		} else {
	//			rerl = rerlIn;
	//		}
	//
	//		if (rerl.lrVal != null) {// we have an identifier (or sth else too?)
	//			final ExpressionResult writes = new ExpressionResult((RValue) null);
	//			final ArrayList<Statement> writeCalls =
	//					mMemoryHandler.getWriteCall(loc, new HeapLValue(startAddress, rerl.lrVal.getCType()),
	//							((RValue) rerl.lrVal).getValue(), rerl.lrVal.getCType());
	//			writes.stmt.addAll(writeCalls);
	//			return writes;
	//		}
	//
	//		Expression newStartAddressBase = null;
	//		Expression newStartAddressOffset = null;
	//		if (startAddress instanceof StructConstructor) {
	//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
	//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
	//		} else {
	//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
	//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
	//		}
	//
	//		// everything for the new Result
	//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
	//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
	//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
	//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
	//
	//		final String[] fieldIds = structType.getFieldIds();
	//		final CType[] fieldTypes = structType.getFieldTypes();
	//
	//		final boolean isUnion = structType instanceof CUnion;
	//		// in a union, only one field of the underlying struct may be initialized
	//		// we do the first, if no fieldname is given, this variable stores whether
	//		// we already initialized a field
	//		boolean unionAlreadyInitialized = false;
	//
	//		for (int i = 0; i < fieldIds.length; i++) {
	//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
	//
	//			final Expression fieldAddressBase = newStartAddressBase;
	//			final Expression fieldAddressOffset =
	//					mStructHandler.computeStructFieldOffset(mMemoryHandler, loc, i, newStartAddressOffset, structType);
	//			final StructConstructor fieldPointer =
	//					MemoryHandler.constructPointerFromBaseAndOffset(fieldAddressBase, fieldAddressOffset, loc);
	//			final HeapLValue fieldHlv = new HeapLValue(fieldPointer, underlyingFieldType);
	//
	//			ExpressionResult fieldWrites = null;
	//
	//			if (isUnion) {
	//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
	//				// TODO: maybe not use auxiliary variables so lavishly
	//				if (!unionAlreadyInitialized && rerl.list.size() == 1
	//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
	//								|| fieldIds[i].equals(rerl.list.get(0).field))
	//						&& (underlyingFieldType instanceof CStruct
	//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
	//					// use the value from the rerl to initialize the union
	//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
	//							rerl.list.get(0));
	//					unionAlreadyInitialized = true;
	//				} else {
	//					// fill in the uninitialized aux variable
	//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
	//
	//					fieldWrites = new ExpressionResult((RValue) null);
	//					fieldWrites.stmt.addAll(mMemoryHandler.getWriteCall(loc, fieldHlv,
	//							new IdentifierExpression(loc, tmpId), underlyingFieldType));
	//					final VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0],
	//							new VarList[] { new VarList(loc, new String[] { tmpId },
	//									main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
	//					fieldWrites.decl.add(auxVarDec);
	//					fieldWrites.auxVars.put(auxVarDec, loc);
	//				}
	//
	//			} else {
	//				if (underlyingFieldType instanceof CPrimitive) {
	//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
	//							i < rerl.list.size() ? rerl.list.get(i) : null);
	//				} else if (underlyingFieldType instanceof CPointer) {
	//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
	//							i < rerl.list.size() ? rerl.list.get(i) : null);
	//				} else if (underlyingFieldType instanceof CArray) {
	//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
	//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
	//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
	//							new LinkedHashMap<VariableDeclaration, ILocation>();
	//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
	//
	//					ExpressionListRecResult arrayInitRerl = null;
	//					if (i < rerl.list.size()) {
	//						arrayInitRerl = rerl.list.get(i);
	//					}
	//
	//					final ExpressionResult aInit =
	//							initArrayOnHeap(main, loc, arrayInitRerl == null ? null : arrayInitRerl.list, fieldPointer,
	//									(CArray) underlyingFieldType);
	//					fieldStmt.addAll(aInit.stmt);
	//					fieldDecl.addAll(aInit.decl);
	//					fieldAuxVars.putAll(aInit.auxVars);
	//					fieldOverApp.addAll(aInit.overappr);
	//
	//					fieldWrites = new ExpressionResult(fieldStmt, null, fieldDecl, fieldAuxVars, fieldOverApp);
	//				} else if (underlyingFieldType instanceof CEnum) {
	//					// like CPrimitive (?)
	//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
	//							i < rerl.list.size() ? rerl.list.get(i) : null);
	//					// throw new UnsupportedSyntaxException(loc, "..");
	//				} else if (underlyingFieldType instanceof CStruct) {
	//					final ExpressionListRecResult fieldRerl =
	//							i < rerl.list.size() ? rerl.list.get(i) : new ExpressionListRecResult();
	//					fieldWrites =
	//							initStructOnHeapFromRERL(main, loc, fieldPointer, fieldRerl, (CStruct) underlyingFieldType);
	//
	//				} else if (underlyingFieldType instanceof CNamed) {
	//					throw new AssertionError("This should not be the case as we took the underlying type.");
	//				} else {
	//					throw new UnsupportedSyntaxException(loc, "..");
	//				}
	//			}
	//			newStmt.addAll(fieldWrites.stmt);
	//			newDecl.addAll(fieldWrites.decl);
	//			newAuxVars.putAll(fieldWrites.auxVars);
	//			newOverappr.addAll(fieldWrites.overappr);
	//		}
	//		final ExpressionResult result = new ExpressionResult(newStmt, new RValue(
	//				MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffset, loc),
	//				structType), newDecl, newAuxVars, newOverappr);
	//		return result;
	//	}
	//
	//	/**
	//	 * Takes a ResultExpressionListRec and a CStruct(type) and generates a StructConstructor with the nesting structure
	//	 * from the CStruct and the values from the RERL. If the RERL is null, the default initialization (int: 0, Ptr:
	//	 * NULL, ...) is used for each entry.
	//	 */
	//	private ExpressionResult makeStructConstructorFromRERL(final Dispatcher main, final ILocation loc,
	//			final ExpressionListRecResult rerlIn, final CStruct structType) {
	//		ExpressionListRecResult rerl = null;
	//		if (rerlIn == null) {
	//			rerl = new ExpressionListRecResult();
	//		} else {
	//			rerl = rerlIn;
	//		}
	//
	//		if (rerl.lrVal != null) {
	//			return new ExpressionResult(rerl.stmt, rerl.lrVal, rerl.decl, rerl.auxVars, rerl.overappr);
	//		}
	//
	//		final boolean isUnion = structType instanceof CUnion;
	//		// in a union, only one field of the underlying struct may be initialized
	//		// we do the first, if no fieldname is given, this variable stores whether
	//		// we already initialized a field
	//		boolean unionAlreadyInitialized = false;
	//
	//		// everything for the new Result
	//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
	//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
	//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
	//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
	//
	//		final String[] fieldIds = structType.getFieldIds();
	//		final CType[] fieldTypes = structType.getFieldTypes();
	//
	//		// the new Arrays for the StructConstructor
	//		final ArrayList<String> fieldIdentifiers = new ArrayList<String>();
	//		final ArrayList<Expression> fieldValues = new ArrayList<Expression>();
	//
	//		for (int i = 0; i < fieldIds.length; i++) {
	//			fieldIdentifiers.add(fieldIds[i]);
	//
	//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
	//
	//			ExpressionResult fieldContents = null;
	//
	//			if (isUnion) {
	//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
	//				// TODO: maybe not use auxiliary variables so lavishly
	//				final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
	//				if (!unionAlreadyInitialized && rerl.list.size() == 1
	//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
	//								|| fieldIds[i].equals(rerl.list.get(0).field))
	//						&& (underlyingFieldType instanceof CStruct
	//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
	//					// use the value from the rerl to initialize the union
	//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, new VariableLHS(loc, tmpId),
	//							underlyingFieldType, rerl.list.get(0));
	//					fieldContents.lrVal = new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType);
	//					unionAlreadyInitialized = true;
	//				} else {
	//					// fill in the uninitialized aux variable
	//					fieldContents =
	//							new ExpressionResult(new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType));
	//				}
	//				final VariableDeclaration auxVarDec =
	//						new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
	//								new String[] { tmpId }, main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
	//				fieldContents.decl.add(auxVarDec);
	//				fieldContents.auxVars.put(auxVarDec, loc);
	//			} else {
	//				if (underlyingFieldType instanceof CPrimitive) {
	//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
	//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
	//				} else if (underlyingFieldType instanceof CPointer) {
	//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
	//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
	//				} else if (underlyingFieldType instanceof CArray) {
	//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
	//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
	//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
	//							new LinkedHashMap<VariableDeclaration, ILocation>();
	//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
	//
	//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, underlyingFieldType);
	//
	//					ExpressionListRecResult arrayInitRerl = null;
	//					if (i < rerl.list.size()) {
	//						arrayInitRerl = rerl.list.get(i);
	//					}
	//
	//					final Expression fieldEx = new IdentifierExpression(loc, tmpId);
	//					final HeapLValue lrVal = new HeapLValue(fieldEx, underlyingFieldType);
	//
	//					final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId,
	//							main.mTypeHandler.cType2AstType(loc, underlyingFieldType), loc);
	//					fieldAuxVars.put(tVarDecl, loc);
	//					fieldDecl.add(tVarDecl);
	//					final VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
	//					final ExpressionResult aInit = main.mCHandler.getInitHandler().initBoogieArray(main, loc,
	//							arrayInitRerl == null ? null : arrayInitRerl.list, fieldLHS, (CArray) underlyingFieldType);
	//
	//					fieldStmt.addAll(aInit.stmt);
	//					fieldDecl.addAll(aInit.decl);
	//					fieldAuxVars.putAll(aInit.auxVars);
	//					fieldOverApp.addAll(aInit.overappr);
	//
	//					fieldContents = new ExpressionResult(fieldStmt, lrVal, fieldDecl, fieldAuxVars, fieldOverApp);
	//				} else if (underlyingFieldType instanceof CEnum) {
	//					// like CPrimitive
	//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
	//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
	//				} else if (underlyingFieldType instanceof CStruct) {
	//					if (i < rerl.list.size()) {
	//						fieldContents = makeStructConstructorFromRERL(main, loc, rerl.list.get(i),
	//								(CStruct) underlyingFieldType);
	//					} else {
	//						fieldContents = makeStructConstructorFromRERL(main, loc, new ExpressionListRecResult(),
	//								(CStruct) underlyingFieldType);
	//					}
	//				} else if (underlyingFieldType instanceof CNamed) {
	//					throw new AssertionError("This should not be the case as we took the underlying type.");
	//				} else {
	//					throw new UnsupportedSyntaxException(loc, "..");
	//				}
	//			}
	//			newStmt.addAll(fieldContents.stmt);
	//			newDecl.addAll(fieldContents.decl);
	//			newAuxVars.putAll(fieldContents.auxVars);
	//			newOverappr.addAll(fieldContents.overappr);
	//			if (fieldContents.lrVal instanceof HeapLValue) {
	//				fieldValues.add(((HeapLValue) fieldContents.lrVal).getAddress());
	//			} else if (fieldContents.lrVal instanceof RValue) {
	//				fieldValues.add(((RValue) fieldContents.lrVal).getValue());
	//			} else {
	//				throw new AssertionError();
	//			}
	//		}
	////		final StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
	//		final StructConstructor sc = new StructConstructor(loc, //new InferredType(Type.Struct),
	//				fieldIdentifiers.toArray(new String[fieldIdentifiers.size()]),
	//				fieldValues.toArray(new Expression[fieldValues.size()]));
	//
	//		final ExpressionResult result =
	//				new ExpressionResult(newStmt, new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
	//		return result;
	//	}
	//
	//	private Expression getDefaultValueForSimpleType(final ILocation loc, final CType cType) {
	//		if (cType instanceof CPrimitive) {
	//			final CPrimitive cPrimitive = (CPrimitive) cType;
	//			switch (cPrimitive.getGeneralType()) {
	//			case INTTYPE:
	//				return mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive,
	//						BigInteger.ZERO);
	//			case FLOATTYPE:
	//				// TODO: which methods in expression translation to use??
	//				//				if (cPrimitive.getType().equals(CPrimitives.FLOAT)) {
	//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
	//				//				} else if (cPrimitive.getType().equals(CPrimitives.DOUBLE)) {
	//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
	//				//				} else if (cPrimitive.getType().equals(CPrimitives.LONGDOUBLE)) {
	//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
	//				//				} else {
	//				//					throw new UnsupportedOperationException("UNsopported Floating Type");
	//				//				}
	//				return mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive,
	//						BigDecimal.ZERO);
	//			case VOID:
	//				throw new AssertionError("cannot initialize something that has type void");
	//			default:
	//				throw new AssertionError("unknown category of type");
	//			}
	//		} else if (cType instanceof CEnum) {
	//			return mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
	//					BigInteger.ZERO);
	//		} else if (cType instanceof CPointer) {
	//			return mExpressionTranslation.constructNullPointer(loc);
	//		} else {
	//			throw new UnsupportedOperationException("missing case?");
	//		}
	//	}


//	/**
//	 * Initializes an array that lies on heap, either with some given values or to its default values.
//	 *
//	 * @param list
//	 *            The values that the array should be initialized with, null for default init
//	 * @param startAddress
//	 *            The address on the heap that the array starts at
//	 * @param arrayType
//	 *            The type of the array (containing its size and value type)
//	 * @return a list of statements that do the initialization
//	 */
//	private ExpressionResult initArrayOnHeap(final Dispatcher main, final ILocation loc,
//			final List<ExpressionListRecResult> list, final Expression startAddress, final CArray arrayType) {
//		final List<Statement> stmt = new ArrayList<>();
//		final List<Declaration> decl = new ArrayList<>();
//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
//		final List<Overapprox> overApp = new ArrayList<>();
//
//		final Expression sizeOfCell = mMemoryHandler.calculateSizeOf(loc, arrayType.getValueType());
//		final RValue[] dimensions = arrayType.getDimensions();
//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
//		if (dimBigInteger == null) {
//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
//		}
//		final int currentSizeInt = dimBigInteger.intValue();
//
//		Expression newStartAddressBase = null;
//		Expression newStartAddressOffset = null;
//		if (startAddress instanceof StructConstructor) {
//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
//		} else {
//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
//		}
//
//		if (dimensions.length == 1) {
//			// RValue val = null;
//
//			for (int i = 0; i < currentSizeInt; i++) {
//				CType valueType = arrayType.getValueType().getUnderlyingType();
//				if (valueType instanceof CEnum) {
//					valueType = new CPrimitive(CPrimitives.INT);
//				}
//
//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
//				Expression writeOffset =
//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), sizeOfCell,
//								mExpressionTranslation.getCTypeOfPointerComponents());
//
//				writeOffset = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
//						newStartAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(), writeOffset,
//						mExpressionTranslation.getCTypeOfPointerComponents());
//
//				final Expression writeLocation =
//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, writeOffset, loc);
//
//				// TODO: we may need to pass statements, decls, ...
//				if (list != null && list.size() > i && list.get(i).getLrVal() != null) {
//					final RValue val = (RValue) list.get(i).getLrVal();
//					decl.addAll(list.get(i).getDeclarations());
//					auxVars.putAll(list.get(i).getAuxVars());
//					stmt.addAll(list.get(i).getStatements());
//					overApp.addAll(list.get(i).getOverapprs());
//					stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
//							val.getValue(), val.getCType()));
//				} else {
//					if (valueType instanceof CArray) {
//						throw new AssertionError(
//								"this should not be the case as we are in the inner/outermost array right??");
//					} else if (valueType instanceof CStruct) {
//						final ExpressionResult sInit = initStructOnHeapFromRERL(main, loc, writeLocation,
//								list != null && list.size() > i ? list.get(i) : null, (CStruct) valueType);
//						stmt.addAll(sInit.stmt);
//						decl.addAll(sInit.decl);
//						auxVars.putAll(sInit.auxVars);
//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer) {
//						final ExpressionResult pInit =
//								main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType, null);
//						assert pInit.stmt.isEmpty() && pInit.decl.isEmpty() && pInit.auxVars.isEmpty();
//						final RValue val = (RValue) pInit.lrVal;
//						stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType),
//								val.getValue(), val.getCType()));
//					} else {
//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
//					}
//				}
//			}
//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
//		} else {
//			for (int i = 0; i < currentSizeInt; i++) {
//				Expression newStartAddressOffsetInner = newStartAddressOffset;
//
//				Expression blockOffset = sizeOfCell;
//				for (int j = 1; j < dimensions.length; j++) {
//					blockOffset =
//							mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
//									dimensions[j].getValue(), (CPrimitive) dimensions[j].getCType(), blockOffset,
//									mExpressionTranslation.getCTypeOfPointerComponents());
//				}
//				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(loc,
//						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
//				blockOffset =
//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
//								iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), blockOffset,
//								mExpressionTranslation.getCTypeOfPointerComponents());
//
//				newStartAddressOffsetInner =
//						mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
//								newStartAddressOffsetInner, mExpressionTranslation.getCTypeOfPointerComponents(),
//								blockOffset, mExpressionTranslation.getCTypeOfPointerComponents());
//
//				final ArrayList<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
//				innerDims.remove(0);// TODO ??
//				final CArray innerArrayType =
//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
//
//				final ExpressionResult initRex = initArrayOnHeap(main, loc, list != null ? list.get(i).list : null,
//						MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffsetInner,
//								loc),
//						innerArrayType);
//				stmt.addAll(initRex.stmt);
//				decl.addAll(initRex.decl);
//				auxVars.putAll(initRex.auxVars);
//				overApp.addAll(initRex.overappr);
//			}
//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
//		}
//	}

//	/**
//	 * Initializes an array that is represented as a boogie array, either with some given values or to its default
//	 * values.
//	 *
//	 * @param list
//	 *            The values that the array should be initialized with, null for default init
//	 * @param innerArrayAccessLHS
//	 *            Something representing the array that is to be initialized currently (in case of a nested array this
//	 *            may again represent an arrayAccess, otherwise the array identifier)
//	 * @param arrayType
//	 *            The type of the array (containing its size and value type)
//	 * @return a list of statements that do the initialization
//	 */
//	private ExpressionResult initBoogieArray(final Dispatcher main, final ILocation loc,
//			final List<ExpressionListRecResult> list, final LeftHandSide innerArrayAccessLHS, final CArray arrayType) {
//		final List<Statement> stmt = new ArrayList<Statement>();
//		final List<Declaration> decl = new ArrayList<>();
//		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
//		final List<Overapprox> overApp = new ArrayList<>();
//
//		final RValue[] dimensions = arrayType.getDimensions();
//		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
//		if (dimBigInteger == null) {
//			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
//		}
//		final int currentSizeInt = dimBigInteger.intValue();
//
//		if (dimensions.length == 1) {
//			RValue val = null;
//
//			for (int i = 0; i < currentSizeInt; i++) {
//				if (list != null && list.size() > i && list.get(i).lrVal != null) {
//					// we have a value to initialize with
//					final CType valueType = arrayType.getValueType().getUnderlyingType();
//					main.mCHandler.convert(loc, list.get(i), valueType);
//					val = (RValue) list.get(i).lrVal;
//					decl.addAll(list.get(i).decl);
//					auxVars.putAll(list.get(i).auxVars);
//					stmt.addAll(list.get(i).stmt);
//					overApp.addAll(list.get(i).overappr);
//				} else {
//					// do default initialization
//					final CType valueType = arrayType.getValueType().getUnderlyingType();
//
//					if (valueType instanceof CArray) {
//						throw new AssertionError(
//								"this should not be the case as we are in the inner/outermost array right??");
//					} else if (valueType instanceof CStruct) {
//						final ExpressionResult sInit =
//								makeStructConstructorFromRERL(main, loc, null, (CStruct) valueType);
//						stmt.addAll(sInit.stmt);
//						decl.addAll(sInit.decl);
//						auxVars.putAll(sInit.auxVars);
//						overApp.addAll(sInit.overappr);
//						val = (RValue) sInit.lrVal;
//					} else if (valueType instanceof CPrimitive || valueType instanceof CPointer
//							|| valueType instanceof CEnum) {
//						val = (RValue) main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null, valueType,
//								null).lrVal;
//					} else {
//						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
//					}
//				}
//				Expression[] newIndices = null;
//				LeftHandSide newLHS = null;
//				final CPrimitive indexType = (CPrimitive) dimensions[0].getCType();
//				final Expression index =
//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
//				if (innerArrayAccessLHS instanceof ArrayLHS) {
//					final ArrayList<Expression> innerIndices =
//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
//					innerIndices.add(index);
//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
//				} else {
//					newIndices = new Expression[] { index };
//					newLHS = innerArrayAccessLHS;
//				}
//
//				final ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
//				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { arrayAccessLHS },
//						new Expression[] { val.getValue() });
//				addOverApprToStatementAnnots(overApp, assignment);
//				stmt.add(assignment);
//			}
//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
//		} else {
//			for (int i = 0; i < currentSizeInt; i++) {
//
//				Expression[] newIndices = null;
//				LeftHandSide newLHS = null;
//
//				// 2015-10-24 Matthias: I don't understand where I can take the
//				// type of the index from. As a workaround I take signed int.
//				final CPrimitive indexType = new CPrimitive(CPrimitives.INT);
//				final Expression index =
//						mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
//				if (innerArrayAccessLHS instanceof ArrayLHS) {
//					final ArrayList<Expression> innerIndices =
//							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
//					innerIndices.add(index);
//					newIndices = innerIndices.toArray(new Expression[innerIndices.size()]);
//					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
//				} else {
//					newIndices = new Expression[] { index };
//					newLHS = innerArrayAccessLHS;
//				}
//
//				final List<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
//				innerDims.remove(0);// TODO ??
//				final CArray innerArrayType =
//						new CArray(innerDims.toArray(new RValue[innerDims.size()]), arrayType.getValueType());
//
//				final List<ExpressionListRecResult> listRecCall;
//				if (list == null) {
//					listRecCall = null;
//				} else if (list.size() - 1 < i) {
//					listRecCall = null;
//				} else {
//					listRecCall = list.get(i).list;
//				}
//				final ExpressionResult initRex =
//						initBoogieArray(main, loc, listRecCall, new ArrayLHS(loc, newLHS, newIndices), innerArrayType);
//				stmt.addAll(initRex.stmt);
//				decl.addAll(initRex.decl);
//				auxVars.putAll(initRex.auxVars);
//				overApp.addAll(initRex.overappr);
//			}
//			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
//		}
//		// return arrayWrites;
//	}
//
//	/**
//	 * Generate the write calls for the initialization of the struct onHeap.
//	 */
//	private ExpressionResult initStructOnHeapFromRERL(final Dispatcher main, final ILocation loc,
//			final Expression startAddress, final ExpressionListRecResult rerlIn, final CStruct structType) {
//		ExpressionListRecResult rerl = null;
//		if (rerlIn == null) {
//			rerl = new ExpressionListRecResult();
//		} else {
//			rerl = rerlIn;
//		}
//
//		if (rerl.lrVal != null) {// we have an identifier (or sth else too?)
//			final ExpressionResult writes = new ExpressionResult((RValue) null);
//			final ArrayList<Statement> writeCalls =
//					mMemoryHandler.getWriteCall(loc, new HeapLValue(startAddress, rerl.lrVal.getCType()),
//							((RValue) rerl.lrVal).getValue(), rerl.lrVal.getCType());
//			writes.stmt.addAll(writeCalls);
//			return writes;
//		}
//
//		Expression newStartAddressBase = null;
//		Expression newStartAddressOffset = null;
//		if (startAddress instanceof StructConstructor) {
//			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
//			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
//		} else {
//			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
//			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
//		}
//
//		// everything for the new Result
//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
//
//		final String[] fieldIds = structType.getFieldIds();
//		final CType[] fieldTypes = structType.getFieldTypes();
//
//		final boolean isUnion = structType instanceof CUnion;
//		// in a union, only one field of the underlying struct may be initialized
//		// we do the first, if no fieldname is given, this variable stores whether
//		// we already initialized a field
//		boolean unionAlreadyInitialized = false;
//
//		for (int i = 0; i < fieldIds.length; i++) {
//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
//
//			final Expression fieldAddressBase = newStartAddressBase;
//			final Expression fieldAddressOffset =
//					mStructHandler.computeStructFieldOffset(mMemoryHandler, loc, i, newStartAddressOffset, structType);
//			final StructConstructor fieldPointer =
//					MemoryHandler.constructPointerFromBaseAndOffset(fieldAddressBase, fieldAddressOffset, loc);
//			final HeapLValue fieldHlv = new HeapLValue(fieldPointer, underlyingFieldType);
//
//			ExpressionResult fieldWrites = null;
//
//			if (isUnion) {
//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
//				// TODO: maybe not use auxiliary variables so lavishly
//				if (!unionAlreadyInitialized && rerl.list.size() == 1
//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
//								|| fieldIds[i].equals(rerl.list.get(0).field))
//						&& (underlyingFieldType instanceof CStruct
//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
//					// use the value from the rerl to initialize the union
//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
//							rerl.list.get(0));
//					unionAlreadyInitialized = true;
//				} else {
//					// fill in the uninitialized aux variable
//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
//
//					fieldWrites = new ExpressionResult((RValue) null);
//					fieldWrites.stmt.addAll(mMemoryHandler.getWriteCall(loc, fieldHlv,
//							new IdentifierExpression(loc, tmpId), underlyingFieldType));
//					final VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0],
//							new VarList[] { new VarList(loc, new String[] { tmpId },
//									main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
//					fieldWrites.decl.add(auxVarDec);
//					fieldWrites.auxVars.put(auxVarDec, loc);
//				}
//
//			} else {
//				if (underlyingFieldType instanceof CPrimitive) {
//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
//							i < rerl.list.size() ? rerl.list.get(i) : null);
//				} else if (underlyingFieldType instanceof CPointer) {
//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
//							i < rerl.list.size() ? rerl.list.get(i) : null);
//				} else if (underlyingFieldType instanceof CArray) {
//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
//							new LinkedHashMap<VariableDeclaration, ILocation>();
//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
//
//					ExpressionListRecResult arrayInitRerl = null;
//					if (i < rerl.list.size()) {
//						arrayInitRerl = rerl.list.get(i);
//					}
//
//					final ExpressionResult aInit =
//							initArrayOnHeap(main, loc, arrayInitRerl == null ? null : arrayInitRerl.list, fieldPointer,
//									(CArray) underlyingFieldType);
//					fieldStmt.addAll(aInit.stmt);
//					fieldDecl.addAll(aInit.decl);
//					fieldAuxVars.putAll(aInit.auxVars);
//					fieldOverApp.addAll(aInit.overappr);
//
//					fieldWrites = new ExpressionResult(fieldStmt, null, fieldDecl, fieldAuxVars, fieldOverApp);
//				} else if (underlyingFieldType instanceof CEnum) {
//					// like CPrimitive (?)
//					fieldWrites = main.mCHandler.getInitHandler().makeVarInitializationWithGivenReturnValue(loc, main, fieldHlv, underlyingFieldType,
//							i < rerl.list.size() ? rerl.list.get(i) : null);
//					// throw new UnsupportedSyntaxException(loc, "..");
//				} else if (underlyingFieldType instanceof CStruct) {
//					final ExpressionListRecResult fieldRerl =
//							i < rerl.list.size() ? rerl.list.get(i) : new ExpressionListRecResult();
//					fieldWrites =
//							initStructOnHeapFromRERL(main, loc, fieldPointer, fieldRerl, (CStruct) underlyingFieldType);
//
//				} else if (underlyingFieldType instanceof CNamed) {
//					throw new AssertionError("This should not be the case as we took the underlying type.");
//				} else {
//					throw new UnsupportedSyntaxException(loc, "..");
//				}
//			}
//			newStmt.addAll(fieldWrites.stmt);
//			newDecl.addAll(fieldWrites.decl);
//			newAuxVars.putAll(fieldWrites.auxVars);
//			newOverappr.addAll(fieldWrites.overappr);
//		}
//		final ExpressionResult result = new ExpressionResult(newStmt, new RValue(
//				MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffset, loc),
//				structType), newDecl, newAuxVars, newOverappr);
//		return result;
//	}
//
//	/**
//	 * Takes a ResultExpressionListRec and a CStruct(type) and generates a StructConstructor with the nesting structure
//	 * from the CStruct and the values from the RERL. If the RERL is null, the default initialization (int: 0, Ptr:
//	 * NULL, ...) is used for each entry.
//	 */
//	private ExpressionResult makeStructConstructorFromRERL(final Dispatcher main, final ILocation loc,
//			final ExpressionListRecResult rerlIn, final CStruct structType) {
//		ExpressionListRecResult rerl = null;
//		if (rerlIn == null) {
//			rerl = new ExpressionListRecResult();
//		} else {
//			rerl = rerlIn;
//		}
//
//		if (rerl.lrVal != null) {
//			return new ExpressionResult(rerl.stmt, rerl.lrVal, rerl.decl, rerl.auxVars, rerl.overappr);
//		}
//
//		final boolean isUnion = structType instanceof CUnion;
//		// in a union, only one field of the underlying struct may be initialized
//		// we do the first, if no fieldname is given, this variable stores whether
//		// we already initialized a field
//		boolean unionAlreadyInitialized = false;
//
//		// everything for the new Result
//		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
//		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
//		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
//		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();
//
//		final String[] fieldIds = structType.getFieldIds();
//		final CType[] fieldTypes = structType.getFieldTypes();
//
//		// the new Arrays for the StructConstructor
//		final ArrayList<String> fieldIdentifiers = new ArrayList<String>();
//		final ArrayList<Expression> fieldValues = new ArrayList<Expression>();
//
//		for (int i = 0; i < fieldIds.length; i++) {
//			fieldIdentifiers.add(fieldIds[i]);
//
//			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();
//
//			ExpressionResult fieldContents = null;
//
//			if (isUnion) {
//				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
//				// TODO: maybe not use auxiliary variables so lavishly
//				final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
//				if (!unionAlreadyInitialized && rerl.list.size() == 1
//						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
//								|| fieldIds[i].equals(rerl.list.get(0).field))
//						&& (underlyingFieldType instanceof CStruct
//								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
//					// use the value from the rerl to initialize the union
//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, new VariableLHS(loc, tmpId),
//							underlyingFieldType, rerl.list.get(0));
//					fieldContents.lrVal = new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType);
//					unionAlreadyInitialized = true;
//				} else {
//					// fill in the uninitialized aux variable
//					fieldContents =
//							new ExpressionResult(new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType));
//				}
//				final VariableDeclaration auxVarDec =
//						new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
//								new String[] { tmpId }, main.mTypeHandler.cType2AstType(loc, underlyingFieldType)) });
//				fieldContents.decl.add(auxVarDec);
//				fieldContents.auxVars.put(auxVarDec, loc);
//			} else {
//				if (underlyingFieldType instanceof CPrimitive) {
//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
//				} else if (underlyingFieldType instanceof CPointer) {
//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
//				} else if (underlyingFieldType instanceof CArray) {
//					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
//					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
//					final Map<VariableDeclaration, ILocation> fieldAuxVars =
//							new LinkedHashMap<VariableDeclaration, ILocation>();
//					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();
//
//					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, underlyingFieldType);
//
//					ExpressionListRecResult arrayInitRerl = null;
//					if (i < rerl.list.size()) {
//						arrayInitRerl = rerl.list.get(i);
//					}
//
//					final Expression fieldEx = new IdentifierExpression(loc, tmpId);
//					final HeapLValue lrVal = new HeapLValue(fieldEx, underlyingFieldType);
//
//					final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId,
//							main.mTypeHandler.cType2AstType(loc, underlyingFieldType), loc);
//					fieldAuxVars.put(tVarDecl, loc);
//					fieldDecl.add(tVarDecl);
//					final VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
//					final ExpressionResult aInit = main.mCHandler.getInitHandler().initBoogieArray(main, loc,
//							arrayInitRerl == null ? null : arrayInitRerl.list, fieldLHS, (CArray) underlyingFieldType);
//
//					fieldStmt.addAll(aInit.stmt);
//					fieldDecl.addAll(aInit.decl);
//					fieldAuxVars.putAll(aInit.auxVars);
//					fieldOverApp.addAll(aInit.overappr);
//
//					fieldContents = new ExpressionResult(fieldStmt, lrVal, fieldDecl, fieldAuxVars, fieldOverApp);
//				} else if (underlyingFieldType instanceof CEnum) {
//					// like CPrimitive
//					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, (VariableLHS) null,
//							underlyingFieldType, i < rerl.list.size() ? rerl.list.get(i) : null);
//				} else if (underlyingFieldType instanceof CStruct) {
//					if (i < rerl.list.size()) {
//						fieldContents = makeStructConstructorFromRERL(main, loc, rerl.list.get(i),
//								(CStruct) underlyingFieldType);
//					} else {
//						fieldContents = makeStructConstructorFromRERL(main, loc, new ExpressionListRecResult(),
//								(CStruct) underlyingFieldType);
//					}
//				} else if (underlyingFieldType instanceof CNamed) {
//					throw new AssertionError("This should not be the case as we took the underlying type.");
//				} else {
//					throw new UnsupportedSyntaxException(loc, "..");
//				}
//			}
//			newStmt.addAll(fieldContents.stmt);
//			newDecl.addAll(fieldContents.decl);
//			newAuxVars.putAll(fieldContents.auxVars);
//			newOverappr.addAll(fieldContents.overappr);
//			if (fieldContents.lrVal instanceof HeapLValue) {
//				fieldValues.add(((HeapLValue) fieldContents.lrVal).getAddress());
//			} else if (fieldContents.lrVal instanceof RValue) {
//				fieldValues.add(((RValue) fieldContents.lrVal).getValue());
//			} else {
//				throw new AssertionError();
//			}
//		}
////		final StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
//		final StructConstructor sc = new StructConstructor(loc, //new InferredType(Type.Struct),
//				fieldIdentifiers.toArray(new String[fieldIdentifiers.size()]),
//				fieldValues.toArray(new Expression[fieldValues.size()]));
//
//		final ExpressionResult result =
//				new ExpressionResult(newStmt, new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
//		return result;
//	}
//
//	private Expression getDefaultValueForSimpleType(final ILocation loc, final CType cType) {
//		if (cType instanceof CPrimitive) {
//			final CPrimitive cPrimitive = (CPrimitive) cType;
//			switch (cPrimitive.getGeneralType()) {
//			case INTTYPE:
//				return mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive,
//						BigInteger.ZERO);
//			case FLOATTYPE:
//				// TODO: which methods in expression translation to use??
//				//				if (cPrimitive.getType().equals(CPrimitives.FLOAT)) {
//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0f").getValue();
//				//				} else if (cPrimitive.getType().equals(CPrimitives.DOUBLE)) {
//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0").getValue();
//				//				} else if (cPrimitive.getType().equals(CPrimitives.LONGDOUBLE)) {
//				//					rhs = mExpressionTranslation.translateFloatingLiteral(loc, "0.0l").getValue();
//				//				} else {
//				//					throw new UnsupportedOperationException("UNsopported Floating Type");
//				//				}
//				return mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive,
//						BigDecimal.ZERO);
//			case VOID:
//				throw new AssertionError("cannot initialize something that has type void");
//			default:
//				throw new AssertionError("unknown category of type");
//			}
//		} else if (cType instanceof CEnum) {
//			return mExpressionTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
//					BigInteger.ZERO);
//		} else if (cType instanceof CPointer) {
//			return mExpressionTranslation.constructNullPointer(loc);
//		} else {
//			throw new UnsupportedOperationException("missing case?");
//		}
//	}

}
