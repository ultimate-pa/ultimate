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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
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
			final CType cTypeRaw, final Result initializerRaw) {

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

		return null;
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

	private static void addOverApprToStatementAnnots(final List<Overapprox> overappr, final Statement stm) {
		for (final Overapprox overapprItem : overappr) {
			overapprItem.annotate(stm);
		}
	}


	public List<Declaration> declareInitializationInfrastructure(final Dispatcher main, final ILocation loc) {
		return Collections.emptyList();
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

}
