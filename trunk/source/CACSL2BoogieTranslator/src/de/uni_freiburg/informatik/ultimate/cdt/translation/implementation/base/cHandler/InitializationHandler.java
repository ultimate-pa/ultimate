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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListRecResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class InitializationHandler {

	private final FunctionHandler mFunctionHandler;

	private final StructHandler mStructHandler;

	private final MemoryHandler mMemoryHandler;

	private final AExpressionTranslation mExpressionTranslation;	

	public InitializationHandler(
			FunctionHandler functionHandler, StructHandler structHandler,
			MemoryHandler memoryHandler, AExpressionTranslation expressionTranslation) {
		super();
		mFunctionHandler = functionHandler;
		mStructHandler = structHandler;
		mMemoryHandler = memoryHandler;
		mExpressionTranslation = expressionTranslation;
	}


	/**
	 * Initializes global variables recursively, according to ISO/IEC 9899:TC3,
	 * 6.7.8 §10:<br>
	 * <blockquote
	 * cite="http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf"><i>"If
	 * an object that has automatic storage duration is not initialized
	 * explicitly, its value is indeterminate. If an object that has static
	 * storage duration is not initialized explicitly, then:
	 * <ul>
	 * <li>if it has pointer type, it is initialized to a null pointer;</li>
	 * <li>if it has arithmetic type, it is initialized to (positive or
	 * unsigned) zero;</li>
	 * <li>if it is an aggregate, every member is initialized (recursively)
	 * according to these rules;</li>
	 * <li>if it is a union, the first named member is initialized (recursively)
	 * according to these rules."</li>
	 * </ul>
	 * </i></blockquote> where (from 6.2.5 Types §21): <blockquote
	 * cite="http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf"
	 * ><i>"Arithmetic types and pointer types are collectively called scalar
	 * types. Array and structure types are collectively called aggregate
	 * types."</i></blockquote>
	 * 
	 * -- version for Expression that have an identifier in the program, i.e. where 
	 *  onHeap is determined via the corresponding store in the CHandler  --
	 * 
	 * @param lhs
	 *            the LeftHandSide to initialize. If this is null, the initializing value
	 *            is returned in the lrValue of the returned ResultExpression which otherwise
	 *            is null.
	 *            (Detail: if we initialize something onHeap, lhs may not be null)
	 * @param cType
	 *            The CType of the initialized variable
	 * 
	 * @return 
	 */
	public ExpressionResult initVar(ILocation loc, Dispatcher main,
			LeftHandSide lhs, CType cType, ExpressionResult initializerRaw) {

		boolean onHeap = false;
		if (lhs != null && lhs instanceof VariableLHS) {
			onHeap = ((CHandler )main.mCHandler).isHeapVar(((VariableLHS) lhs).getIdentifier());
		}

		LRValue var = null;
		if (onHeap) {
			var = new HeapLValue(new IdentifierExpression(loc, ((VariableLHS)lhs).getIdentifier()), cType);
		} else {
			var = lhs == null ? null : new LocalLValue(lhs, cType);
		}

		if (var == null) {
			return initVar(loc, main, 
					cType, initializerRaw);
		} else {
			return initVar(loc, main, 
					var, cType, initializerRaw);
		}
	}


	/**
	 * Helper for variable initialization. This version does not take any form of the initialized
	 * variable as an argument but instead returns a ResultExpression with an lrValue that can be 
	 * stored in such a variable.
	 */
	private ExpressionResult initVar(ILocation loc, Dispatcher main,
			CType cType, ExpressionResult initializerRaw) {
		final CType lCType = cType.getUnderlyingType();

		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
		LRValue lrVal = null;

		//if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
		//carry over
		ExpressionResult initializer = null;
		if (initializerRaw != null) {
			initializer = 
					initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			stmt.addAll(initializer.stmt);
			decl.addAll(initializer.decl);
			overappr.addAll(initializer.overappr);
			auxVars.putAll(initializer.auxVars);
		}

		final VariableLHS lhs = null;

		Expression rhs = null;
		if (lCType instanceof CPrimitive) {
			switch (((CPrimitive) lCType).getGeneralType()) {
			case INTTYPE:
				if (initializer == null) {
					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, (CPrimitive) lCType, BigInteger.ZERO);
				} else {
					initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
					main.mCHandler.convert(loc, initializer, lCType);
					rhs = initializer.lrVal.getValue();
				}
				break;
			case FLOATTYPE:
				if (initializer == null) {
					rhs = new RealLiteral(loc, SFO.NR0F);
				} else {
					initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
					main.mCHandler.convert(loc, initializer, lCType);
					rhs = initializer.lrVal.getValue();
				}
				break;
			case VOID:
			default:
				throw new AssertionError("unknown type to init");
			}

			lrVal = new RValue(rhs, lCType);
		} else if (lCType instanceof CPointer) {
			if (initializer == null) {
				rhs = mExpressionTranslation.constructNullPointer(loc);
			} else {
				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
				if (initializerUnderlyingType instanceof CPointer
						|| initializerUnderlyingType instanceof CArray) {
					rhs = initializer.lrVal.getValue();
				} else if (initializerUnderlyingType instanceof CPrimitive 
						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == GENERALPRIMITIVE.INTTYPE){
					final BigInteger pointerOffsetValue = mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
					if (pointerOffsetValue == null) {
						throw new IllegalArgumentException("unable to understand " + initializer.lrVal);
					}
					if (pointerOffsetValue.equals(BigInteger.ZERO)) {
						rhs = mExpressionTranslation.constructNullPointer(loc);
					} else {
						final BigInteger pointerBaseValue = BigInteger.ZERO;
						rhs = mExpressionTranslation.constructPointerForIntegerValues(loc, pointerBaseValue, pointerOffsetValue);
					}
				} else {
					throw new AssertionError("trying to initialize a pointer with something different from int and pointer");
				}
			}

			lrVal = new RValue(rhs, lCType);
		} else if (lCType instanceof CArray) {

			if (initializer == null) {
				final ExpressionResult aInit = initBoogieArray(main, loc,
						null, lhs, (CArray) lCType);
				stmt.addAll(aInit.stmt);
				decl.addAll(aInit.decl);
				auxVars.putAll(aInit.auxVars);
			} else if (initializer instanceof ExpressionListRecResult) {
				final ExpressionResult aInit = initBoogieArray(main, loc,
						((ExpressionListRecResult) initializer).list, lhs, (CArray) lCType);
				stmt.addAll(aInit.stmt);
				decl.addAll(aInit.decl);
				auxVars.putAll(aInit.auxVars);
			} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the corresponding aux vars
				//					stmt.addAll(initializer.stmt);
				//					decl.addAll(initializer.decl);
				//					auxVars.putAll(initializer.auxVars);
			} else {
				assert false;
			}
			//			}
			assert lhs != null;
		} else if (lCType instanceof CStruct) {
			final CStruct structType = (CStruct) lCType;

			final ExpressionResult scRex = makeStructConstructorFromRERL(main, loc, 
					(ExpressionListRecResult) initializer,
					structType);

			stmt.addAll(scRex.stmt);
			decl.addAll(scRex.decl);
			overappr.addAll(scRex.overappr);
			auxVars.putAll(scRex.auxVars);

			lrVal = new RValue(rhs, lCType);
		} else if (lCType instanceof CEnum) {
			if (initializer == null) {
				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, 
						new CPrimitive(PRIMITIVE.INT), BigInteger.ZERO);
			} else {
				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
				rhs = initializer.lrVal.getValue();
			}		
			lrVal = new RValue(rhs, lCType);
		} else {
			final String msg = "Unknown type - don't know how to initialize!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		assert (CHandler.isAuxVarMapcomplete(main.mNameHandler, decl, auxVars));

		// lrVal is null in case we got a lhs to assign to, the initializing value otherwise
		return new ExpressionResult(stmt, lrVal, decl, auxVars, overappr);
	}

	/**
	 * Same as other initVar but with an LRValue as argument, not a LHS
	 * if var is a HeapLValue, something on Heap is initialized, 
	 * if it is a LocalLValue something off the Heap is initialized
	 */
	private ExpressionResult initVar(ILocation loc, Dispatcher main,
			LRValue var, CType cType, ExpressionResult initializerRaw) {
		assert var != null;

		final boolean onHeap = var instanceof HeapLValue;

		final CType lCType = cType.getUnderlyingType();

		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		final ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();

		//if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
		//carry over
		ExpressionResult initializer = null;
		if (initializerRaw != null) {
			initializer = initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			stmt.addAll(initializer.stmt);
			decl.addAll(initializer.decl);
			overappr.addAll(initializer.overappr);
			auxVars.putAll(initializer.auxVars);
		}

		VariableLHS lhs = null;
		if (var instanceof LocalLValue) {
			lhs = (VariableLHS) ((LocalLValue) var).getLHS();
		}
		Expression rhs = null;
		if (lCType instanceof CPrimitive) {
			switch (((CPrimitive) lCType).getGeneralType()) {
			case INTTYPE:
				if (initializer == null) {
					rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, (CPrimitive) lCType, BigInteger.ZERO);
				} else {
					initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
					main.mCHandler.convert(loc, initializer, lCType);
					rhs = initializer.lrVal.getValue();
				}
				break;
			case FLOATTYPE:
				if (initializer == null) {
					rhs = new RealLiteral(loc, SFO.NR0F);
				} else {
					main.mCHandler.convert(loc, initializer, lCType);
					rhs = initializer.lrVal.getValue();
				}
				break;
			case VOID:
			default:
				throw new AssertionError("unknown type to init");
			}
			if (onHeap) {
				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var,
						rhs,
						cType));
			} else {
				assert lhs != null;
				final AssignmentStatement assignment = new AssignmentStatement(loc, 
						new LeftHandSide[] { lhs },
						new Expression[] { rhs } );
				addOverApprToStatementAnnots(overappr, assignment);
				stmt.add(assignment);
			}
		} else if (lCType instanceof CPointer) {
			if (initializer == null) {
				rhs = mExpressionTranslation.constructNullPointer(loc);
			} else {
				final CType initializerUnderlyingType = initializer.lrVal.getCType().getUnderlyingType();
				if (initializerUnderlyingType instanceof CPointer
						|| initializerUnderlyingType instanceof CArray) {
					rhs = initializer.lrVal.getValue();
				} else if (initializerUnderlyingType instanceof CPrimitive 
						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == GENERALPRIMITIVE.INTTYPE){
					final BigInteger offsetValue = mExpressionTranslation.extractIntegerValue((RValue) initializer.lrVal);
					if (offsetValue.equals(BigInteger.ZERO)) {
						rhs = mExpressionTranslation.constructNullPointer(loc);
					} else {
						final Expression base = mExpressionTranslation.constructLiteralForIntegerType(
								loc, mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
						final Expression offset = mExpressionTranslation.constructLiteralForIntegerType(
								loc, mExpressionTranslation.getCTypeOfPointerComponents(), offsetValue);
						rhs = MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
					}
				} else {
					throw new AssertionError("trying to initialize a pointer with something different from int and pointer");
				}
			}
			if (onHeap) {
				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, rhs, lCType));
			} else {
				assert lhs != null;
				final AssignmentStatement assignment = new AssignmentStatement(loc, 
						new LeftHandSide[] { lhs },
						new Expression[] { rhs } );
				addOverApprToStatementAnnots(overappr, assignment);
				stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
						new Expression[] { rhs } ));
			}
		} else if (lCType instanceof CArray) {

			if (onHeap) { 
				final IdentifierExpression arrayAddress = (IdentifierExpression)((HeapLValue) var).getAddress();
				lhs = new VariableLHS(arrayAddress.getLocation(),
						arrayAddress.getIdentifier());			

				//done in simpleDec
//				CallStatement mallocRex = mMemoryHandler.getMallocCall(main, mFunctionHandler,
//						mMemoryHandler.calculateSizeOf(lCType, loc), new LocalLValue(lhs, cType), loc);
//				stmt.add(mallocRex);

				if (initializer == null) {
					final ExpressionResult aInit = initArrayOnHeap(main, loc, 
							null, arrayAddress, (CArray) lCType);				
					stmt.addAll(aInit.stmt);
					decl.addAll(aInit.decl);
					auxVars.putAll(aInit.auxVars);
				} else if (initializer instanceof ExpressionListRecResult) {
					final ExpressionResult aInit = initArrayOnHeap(main, loc, 
							((ExpressionListRecResult) initializer).list, arrayAddress, (CArray) lCType);
					stmt.addAll(aInit.stmt);
					decl.addAll(aInit.decl);
					auxVars.putAll(aInit.auxVars);
				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the corresponding aux vars
					//					stmt.addAll(initializer.stmt);
					//					decl.addAll(initializer.decl);
					//					auxVars.putAll(initializer.auxVars);
				} else {
					assert false;
				}

			} else { //not on Heap
				ExpressionResult initRex = null;
				if (initializer == null) {
					initRex = initBoogieArray(main, loc,
							null, lhs, (CArray) lCType);
				} else if (initializer instanceof ExpressionListRecResult) {
					initRex = initBoogieArray(main, loc,
							((ExpressionListRecResult) initializer).list, lhs, (CArray) lCType);
				} else if (initializer instanceof ExpressionResult) {// we have a variable length array and need the corresponding aux vars
					//					stmt.addAll(initializer.stmt);
					//					decl.addAll(initializer.decl);
					//					auxVars.putAll(initializer.auxVars);
				} else {
					assert false;
				}
				if (initRex != null) {
					stmt.addAll(initRex.stmt);
					decl.addAll(initRex.decl);
					auxVars.putAll(initRex.auxVars);
				}
			}
			assert lhs != null;
		} else if (lCType instanceof CStruct) {
			final CStruct structType = (CStruct) lCType;

			if (onHeap) {
				assert var != null;
				final ExpressionResult heapWrites = initStructOnHeapFromRERL(main, loc, 
						((HeapLValue) var).getAddress(),
						(ExpressionListRecResult) initializer,
						structType);

				stmt.addAll(heapWrites.stmt);
				decl.addAll(heapWrites.decl);
				overappr.addAll(heapWrites.overappr);
				auxVars.putAll(heapWrites.auxVars);
			} else {
				final ExpressionResult scRex = makeStructConstructorFromRERL(main, loc, 
						(ExpressionListRecResult) initializer,
						structType);

				stmt.addAll(scRex.stmt);
				decl.addAll(scRex.decl);
				overappr.addAll(scRex.overappr);
				auxVars.putAll(scRex.auxVars);

				assert lhs != null;
				final Statement assignment = new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { scRex.lrVal.getValue() });
				addOverApprToStatementAnnots(overappr, assignment);
				stmt.add(assignment);
			}
		} else if (lCType instanceof CEnum) {
			if (initializer == null) {
				rhs = mExpressionTranslation.constructLiteralForIntegerType(loc, 
						new CPrimitive(CPrimitive.PRIMITIVE.INT), BigInteger.ZERO);
			} else {
				initializer.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
				rhs = initializer.lrVal.getValue();
			}		
			if (onHeap) {
				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var,
						rhs,
						cType));
			} else {
				assert lhs != null;
				final Statement assignment = new AssignmentStatement(loc, 
						new LeftHandSide[] { lhs },
						new Expression[] { rhs } );
				addOverApprToStatementAnnots(overappr, assignment);
				stmt.add(assignment);
			}
		} else {
			final String msg = "Unknown type - don't know how to initialize!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
//		assert (CHandler.isAuxVarMapcomplete(main, decl, auxVars));

		return new ExpressionResult(stmt, null, decl, auxVars, overappr);
	}


	public static void addOverApprToStatementAnnots(ArrayList<Overapprox> overappr,
			Statement stm) {
		final Map<String, IAnnotations> annots = stm.getPayload().getAnnotations();
		for (final Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
	}

	/**
	 * Initializes an array that lies on heap, either with some given values or to its default values.
	 * @param list The values that the array should be initialized with, null for default init
	 * @param startAddress The address on the heap that the array starts at
	 * @param arrayType The type of the array (containing its size and value type)
	 * @return a list of statements that do the initialization
	 */
	private ExpressionResult initArrayOnHeap(Dispatcher main, ILocation loc, 
			ArrayList<ExpressionListRecResult> list, Expression startAddress,
			CArray arrayType) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ArrayList<Overapprox> overApp = new ArrayList<>();

		final Expression sizeOfCell = mMemoryHandler.calculateSizeOf(loc, arrayType.getValueType()); 
		final RValue[] dimensions = arrayType.getDimensions();
		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
		if (dimBigInteger == null) {
			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		}
		final int currentSizeInt = dimBigInteger.intValue();

		Expression newStartAddressBase = null;
		Expression newStartAddressOffset = null;
		if (startAddress instanceof StructConstructor) {
			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		} else {
			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		}

		if (dimensions.length == 1) {
//			RValue val = null;

			for (int i = 0; i < currentSizeInt; i++) {
				CType valueType = arrayType.getValueType().getUnderlyingType();
				if (valueType instanceof CEnum) {
					valueType = new CPrimitive(PRIMITIVE.INT);
				}
				
				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(
						loc, mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
				Expression writeOffset = mExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_multiply, 
						iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), 
						sizeOfCell, mExpressionTranslation.getCTypeOfPointerComponents()); 
						
				writeOffset = mExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_plus, 
						newStartAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(), 
						writeOffset, mExpressionTranslation.getCTypeOfPointerComponents()); 
						
				final Expression writeLocation = MemoryHandler.constructPointerFromBaseAndOffset(
						newStartAddressBase,
						writeOffset, 
						loc);

//				TODO: we may need to pass statements, decls, ...
				if (list != null && list.size() > i && list.get(i).lrVal != null) {
					final RValue val = (RValue) list.get(i).lrVal; 
					decl.addAll(list.get(i).decl);
					auxVars.putAll(list.get(i).auxVars);
					stmt.addAll(list.get(i).stmt);
					overApp.addAll(list.get(i).overappr);
					stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType), val.getValue(), val.getCType()));
				} else {
					if (valueType instanceof CArray) {
						throw new AssertionError("this should not be the case as we are in the inner/outermost array right??");
					} else if  (valueType instanceof CStruct) {
						final ExpressionResult sInit = initStructOnHeapFromRERL(main, loc, 
								writeLocation, list != null && list.size() > i ? list.get(i) : null, (CStruct) valueType);
						stmt.addAll(sInit.stmt);
						decl.addAll(sInit.decl);
						auxVars.putAll(sInit.auxVars);
					} else if (valueType instanceof CPrimitive 
							|| valueType instanceof CPointer) {
						final ExpressionResult pInit = main.mCHandler.getInitHandler().initVar(loc, main, 
								(VariableLHS) null, valueType, null);
						assert pInit.stmt.isEmpty() && pInit.decl.isEmpty() && pInit.auxVars.isEmpty();
						final RValue val = (RValue) pInit.lrVal;
						stmt.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType), val.getValue(), val.getCType()));
					} else {
						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
					}
				}
			}
			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		} else {
			for (int i = 0; i < currentSizeInt; i++) { 
				Expression newStartAddressOffsetInner = newStartAddressOffset;

				Expression blockOffset = sizeOfCell;
				for (int j = 1; j < dimensions.length; j++) {
					blockOffset = mExpressionTranslation.constructArithmeticExpression(
							loc, IASTBinaryExpression.op_multiply, 
							dimensions[j].getValue(), (CPrimitive) dimensions[j].getCType(), 
							blockOffset, mExpressionTranslation.getCTypeOfPointerComponents()); 
				}
				final Expression iAsExpression = mExpressionTranslation.constructLiteralForIntegerType(
						loc, mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(i));
				blockOffset = mExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_multiply, 
						iAsExpression, mExpressionTranslation.getCTypeOfPointerComponents(), 
						blockOffset, mExpressionTranslation.getCTypeOfPointerComponents()); 

				newStartAddressOffsetInner = mExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_plus, 
						newStartAddressOffsetInner, mExpressionTranslation.getCTypeOfPointerComponents(), 
						blockOffset, mExpressionTranslation.getCTypeOfPointerComponents()); 

				final ArrayList<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
				innerDims.remove(0);//TODO ??
				final CArray innerArrayType = new CArray(innerDims.toArray(new RValue[0]), 
						arrayType.getValueType());

				final ExpressionResult initRex = initArrayOnHeap(main, 
								loc, 
								list != null ? list.get(i).list : null,
										MemoryHandler.constructPointerFromBaseAndOffset(
												newStartAddressBase,
												newStartAddressOffsetInner, 
												loc),
												innerArrayType); 
				stmt.addAll(initRex.stmt);
				decl.addAll(initRex.decl);
				auxVars.putAll(initRex.auxVars);
				overApp.addAll(initRex.overappr);
			}
			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		}
	}

	/**
	 * Initializes an array that is represented as a boogie array, either with some given values 
	 * or to its default values.
	 * @param list The values that the array should be initialized with, null for default init
	 * @param innerArrayAccessLHS Something representing the array that is to be initialized 
	 * currently (in case of a nested array this may again represent an arrayAccess, otherwise 
	 * the array identifier)
	 * @param arrayType The type of the array (containing its size and value type)
	 * @return a list of statements that do the initialization
	 */
	private ExpressionResult initBoogieArray(Dispatcher main, ILocation loc, 
			ArrayList<ExpressionListRecResult> list, LeftHandSide innerArrayAccessLHS,
			CArray arrayType) {
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ArrayList<Overapprox> overApp = new ArrayList<>();

		final RValue[] dimensions = arrayType.getDimensions();
		final BigInteger dimBigInteger = mExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
		if (dimBigInteger == null) {
			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		}
		final int currentSizeInt = dimBigInteger.intValue();

		if (dimensions.length == 1) {
			RValue val = null;

			for (int i = 0; i < currentSizeInt; i++) {
				if (list != null && list.size() > i && list.get(i).lrVal != null) {
					// we have a value to initialize with
					final CType valueType = arrayType.getValueType().getUnderlyingType();
					main.mCHandler.convert(loc, list.get(i), valueType);
					val = (RValue) list.get(i).lrVal;
					decl.addAll(list.get(i).decl);
					auxVars.putAll(list.get(i).auxVars);
					stmt.addAll(list.get(i).stmt);
					overApp.addAll(list.get(i).overappr);
				} else {
					//do default initialization
					final CType valueType = arrayType.getValueType().getUnderlyingType();

					if (valueType instanceof CArray) {
						throw new AssertionError("this should not be the case as we are in the inner/outermost array right??");
					} else if  (valueType instanceof CStruct) {
						final ExpressionResult sInit = makeStructConstructorFromRERL(main, loc, 
								null, (CStruct) valueType);
						stmt.addAll(sInit.stmt);
						decl.addAll(sInit.decl);
						auxVars.putAll(sInit.auxVars);
						overApp.addAll(sInit.overappr);
						val = (RValue) sInit.lrVal;
					} else if (valueType instanceof CPrimitive 
							|| valueType instanceof CPointer
							|| valueType instanceof CEnum) {
						val = (RValue) (main.mCHandler.getInitHandler().initVar(loc, main, 
								(VariableLHS) null, valueType, null)).lrVal;
					} else {
						throw new UnsupportedSyntaxException(loc, "trying to init unknown type " + valueType);
					}
				}
				Expression[] newIndices = null;
				LeftHandSide newLHS = null;
				final CPrimitive indexType = (CPrimitive) dimensions[0].getCType();
				final Expression index = mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
				if (innerArrayAccessLHS instanceof ArrayLHS) {
					final ArrayList<Expression> innerIndices = 
							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
					innerIndices.add(index);
					newIndices = innerIndices.toArray(new Expression[0]);
					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
				} else {
					newIndices = new Expression[] { index };
					newLHS = innerArrayAccessLHS;
				}

				final ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
				final Statement assignment = new AssignmentStatement(loc, 
						new LeftHandSide[] { arrayAccessLHS }, new Expression[] { val.getValue() });
				addOverApprToStatementAnnots(overApp, assignment);
				stmt.add(assignment);
			}
			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		} else {
			for (int i = 0; i < currentSizeInt; i++) { 

				Expression[] newIndices = null;
				LeftHandSide newLHS = null;
				
				// 2015-10-24 Matthias: I don't understand where I can take the
				// type of the index from. As a workaround I take signed int.
				final CPrimitive indexType = new CPrimitive(PRIMITIVE.INT);
				final Expression index = mExpressionTranslation.constructLiteralForIntegerType(loc, indexType, BigInteger.valueOf(i));
				if (innerArrayAccessLHS instanceof ArrayLHS) {
					final ArrayList<Expression> innerIndices = 
							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
					innerIndices.add(index);
					newIndices = innerIndices.toArray(new Expression[0]);
					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
				} else { 
					newIndices = new Expression[] { index };
					newLHS = innerArrayAccessLHS;
				}

				final ArrayList<RValue> innerDims = new ArrayList<RValue>(Arrays.asList(arrayType.getDimensions()));
				innerDims.remove(0);//TODO ??
				final CArray innerArrayType = new CArray(innerDims.toArray(new RValue[0]), 
						arrayType.getValueType());

				final ArrayList<ExpressionListRecResult> listRecCall;
				if (list == null) {
					listRecCall = null;
				} else if (list.size()-1 < i) {
					listRecCall = null;
				} else {
					listRecCall = list.get(i).list;
				}
				final ExpressionResult initRex = initBoogieArray(main, 
								loc, listRecCall,
										new ArrayLHS(loc, newLHS, newIndices), innerArrayType); 
				stmt.addAll(initRex.stmt);
				decl.addAll(initRex.decl);
				auxVars.putAll(initRex.auxVars);
				overApp.addAll(initRex.overappr);
			}
			return new ExpressionResult(stmt, null, decl, auxVars, overApp);
		}
//		return arrayWrites;
	}

	/**
	 * Generate the write calls for the initialization of the struct onHeap.
	 */
	private ExpressionResult initStructOnHeapFromRERL(Dispatcher main, ILocation loc, 
			Expression startAddress, 
			ExpressionListRecResult rerlIn, CStruct structType) {
		ExpressionListRecResult rerl = null;
		if (rerlIn == null) {
			rerl = new ExpressionListRecResult();
		} else {
			rerl = rerlIn;
		}

		if (rerl.lrVal != null) {//we have an identifier (or sth else too?)
			final ExpressionResult writes = new ExpressionResult((RValue) null);
			final ArrayList<Statement> writeCalls = mMemoryHandler.getWriteCall(loc, new HeapLValue(startAddress, rerl.lrVal.getCType()),
					((RValue) rerl.lrVal).getValue(), rerl.lrVal.getCType());
			writes.stmt.addAll(writeCalls);
			return writes;
		}

		Expression newStartAddressBase = null;
		Expression newStartAddressOffset = null;
		if (startAddress instanceof StructConstructor) {
			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		} else {
			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		}	

		//everything for the new Result
		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> newAuxVars =
				new LinkedHashMap<VariableDeclaration, ILocation>();
		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();

		final String[] fieldIds = structType.getFieldIds();
		final CType[] fieldTypes = structType.getFieldTypes();

		final boolean isUnion = (structType instanceof CUnion);
		//in a union, only one field of the underlying struct may be initialized
		//we do the first, if no fieldname is given, this variable stores whether
		//we already initialized a field
		boolean unionAlreadyInitialized = false;

		for (int i = 0; i < fieldIds.length; i++) {
			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();

			final Expression fieldAddressBase = newStartAddressBase;
			final Expression fieldAddressOffset = mStructHandler.computeStructFieldOffset(mMemoryHandler, loc, i, 
					newStartAddressOffset, structType);
			final StructConstructor fieldPointer = MemoryHandler.constructPointerFromBaseAndOffset(
					fieldAddressBase, fieldAddressOffset, loc);
			final HeapLValue fieldHlv = new HeapLValue(fieldPointer, underlyingFieldType);

			ExpressionResult fieldWrites = null; 

			if (isUnion) {
				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
				//TODO: maybe not use auxiliary variables so lavishly
				if (!unionAlreadyInitialized
						&& rerl.list.size() == 1 
						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
						|| fieldIds[i].equals(rerl.list.get(0).field))
						&& (underlyingFieldType instanceof CStruct
								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
					//use the value from the rerl to initialize the union
					fieldWrites = main.mCHandler.getInitHandler().initVar(loc, main, 
							fieldHlv,
							underlyingFieldType, rerl.list.get(0)
							);
					unionAlreadyInitialized = true;
				} else {
					//fill in the uninitialized aux variable
					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);

					fieldWrites = new ExpressionResult((RValue) null);
					fieldWrites.stmt.addAll(mMemoryHandler.getWriteCall(loc, fieldHlv,
							new IdentifierExpression(loc, tmpId),
							underlyingFieldType));
					final VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0], 
							new VarList[] { new VarList(loc, new String[] { tmpId }, 
									main.mTypeHandler.ctype2asttype(loc, underlyingFieldType)) } );
					fieldWrites.decl.add(auxVarDec);
					fieldWrites.auxVars.put(auxVarDec, loc);
				}

			} else {
				if(underlyingFieldType instanceof CPrimitive) {
					fieldWrites = main.mCHandler.getInitHandler().initVar(loc, main, 
							fieldHlv, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CPointer) {
					fieldWrites = main.mCHandler.getInitHandler().initVar(loc, main, 
							fieldHlv, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CArray) {
					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
					final Map<VariableDeclaration, ILocation> fieldAuxVars =
							new LinkedHashMap<VariableDeclaration, ILocation>();
					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();

					ExpressionListRecResult arrayInitRerl = null;
					if (i < rerl.list.size()) {
						arrayInitRerl = rerl.list.get(i);
					}

					final ExpressionResult aInit = initArrayOnHeap(main, loc, 
							arrayInitRerl == null ? null : arrayInitRerl.list, 
									fieldPointer,
									 (CArray) underlyingFieldType);
					fieldStmt.addAll(aInit.stmt);
					fieldDecl.addAll(aInit.decl);
					fieldAuxVars.putAll(aInit.auxVars);
					fieldOverApp.addAll(aInit.overappr);

					fieldWrites = new ExpressionResult(fieldStmt, 
							null,
							fieldDecl, fieldAuxVars, fieldOverApp);
				} else if (underlyingFieldType instanceof CEnum) {
					//like CPrimitive (?)
					fieldWrites = main.mCHandler.getInitHandler().initVar(loc, main, 
							fieldHlv, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
//					throw new UnsupportedSyntaxException(loc, "..");
				} else if (underlyingFieldType instanceof CStruct) {
					final ExpressionListRecResult fieldRerl = i < rerl.list.size() ? 
							rerl.list.get(i) : new ExpressionListRecResult();
							fieldWrites = initStructOnHeapFromRERL(main, loc, 
									fieldPointer, fieldRerl, (CStruct) underlyingFieldType);

				} else if (underlyingFieldType instanceof CNamed) {
					throw new AssertionError("This should not be the case as we took the underlying type.");
				} else {
					throw new UnsupportedSyntaxException(loc, "..");
				}	
			}
			newStmt.addAll(fieldWrites.stmt);
			newDecl.addAll(fieldWrites.decl);
			newAuxVars.putAll(fieldWrites.auxVars);
			newOverappr.addAll(fieldWrites.overappr);
		}
		final ExpressionResult result = new ExpressionResult(newStmt,
				new RValue(MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, newStartAddressOffset, loc), structType), newDecl, newAuxVars, newOverappr);
		return result;
	} 

	/**
	 * Takes a ResultExpressionListRec and a CStruct(type) and generates a StructConstructor with the 
	 * nesting structure from the CStruct and the values from the RERL.
	 * If the RERL is null, the default initialization (int: 0, Ptr: NULL, ...) is used for each entry.
	 */
	private ExpressionResult makeStructConstructorFromRERL(Dispatcher main, ILocation loc, 
			ExpressionListRecResult rerlIn, CStruct structType) {
		ExpressionListRecResult rerl = null;
		if (rerlIn == null) {
			rerl = new ExpressionListRecResult();
		} else {
			rerl = rerlIn;
		}

		if (rerl.lrVal != null) {
			return new ExpressionResult(rerl.stmt, rerl.lrVal, rerl.decl,
					rerl.auxVars, rerl.overappr);
		}

		final boolean isUnion = (structType instanceof CUnion);
		//in a union, only one field of the underlying struct may be initialized
		//we do the first, if no fieldname is given, this variable stores whether
		//we already initialized a field
		boolean unionAlreadyInitialized = false;

		//everything for the new Result
		final ArrayList<Statement> newStmt = new ArrayList<Statement>();
		final ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> newAuxVars =
				new LinkedHashMap<VariableDeclaration, ILocation>();
		final List<Overapprox> newOverappr = new ArrayList<Overapprox>();

		final String[] fieldIds = structType.getFieldIds();
		final CType[] fieldTypes = structType.getFieldTypes();

		//the new Arrays for the StructConstructor
		final ArrayList<String> fieldIdentifiers = new ArrayList<String>();
		final ArrayList<Expression> fieldValues = new ArrayList<Expression>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			final CType underlyingFieldType = fieldTypes[i].getUnderlyingType();

			ExpressionResult fieldContents = null; 

			if (isUnion) {
				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
				//TODO: maybe not use auxiliary variables so lavishly
				final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, underlyingFieldType);
				if (!unionAlreadyInitialized
						&& rerl.list.size() == 1 
						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
						|| fieldIds[i].equals(rerl.list.get(0).field))
						&& (underlyingFieldType instanceof CStruct
								|| rerl.list.get(0).lrVal.getCType().equals(underlyingFieldType))) {
					//use the value from the rerl to initialize the union
					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, 
							new VariableLHS(loc, tmpId),
							underlyingFieldType, rerl.list.get(0));
					fieldContents.lrVal = new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType);
					unionAlreadyInitialized = true;
				} else {
					//fill in the uninitialized aux variable
					fieldContents = new ExpressionResult(
							new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType));
				}
				final VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0], 
						new VarList[] { new VarList(loc, new String[] { tmpId }, 
								main.mTypeHandler.ctype2asttype(loc, underlyingFieldType)) } );
				fieldContents.decl.add(auxVarDec);
				fieldContents.auxVars.put(auxVarDec, loc);
			} else {
				if(underlyingFieldType instanceof CPrimitive) {
					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, 
							(VariableLHS) null, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CPointer) {
					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, 
							(VariableLHS) null, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CArray) {
					final ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
					final ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
					final Map<VariableDeclaration, ILocation> fieldAuxVars =
							new LinkedHashMap<VariableDeclaration, ILocation>();
					final ArrayList<Overapprox> fieldOverApp = new ArrayList<>();

					final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT, underlyingFieldType);

					ExpressionListRecResult arrayInitRerl = null;
					if (i < rerl.list.size()) {
						arrayInitRerl = rerl.list.get(i);
					}

					final Expression fieldEx = new IdentifierExpression(loc, tmpId);
					final HeapLValue lrVal = new HeapLValue(fieldEx, underlyingFieldType);

					final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, 
							main.mTypeHandler.ctype2asttype(loc, underlyingFieldType),
							loc);
					fieldAuxVars.put(tVarDecl, loc);
					fieldDecl.add(tVarDecl);
					final VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
					final ExpressionResult aInit = main.mCHandler.getInitHandler().initBoogieArray(main, loc, 
							arrayInitRerl == null ? null : arrayInitRerl.list, 
									fieldLHS, (CArray) underlyingFieldType);
					
					fieldStmt.addAll(aInit.stmt);
					fieldDecl.addAll(aInit.decl);
					fieldAuxVars.putAll(aInit.auxVars);
					fieldOverApp.addAll(aInit.overappr);

					fieldContents = new ExpressionResult(fieldStmt, lrVal, fieldDecl, 
							fieldAuxVars, fieldOverApp);
				} else if (underlyingFieldType instanceof CEnum) {
					//like CPrimitive
					fieldContents = main.mCHandler.getInitHandler().initVar(loc, main, 
							(VariableLHS) null, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CStruct) {
					if (i < rerl.list.size()) {
						fieldContents = makeStructConstructorFromRERL(main, loc,
								rerl.list.get(i), (CStruct) underlyingFieldType);
					} else {
						fieldContents = makeStructConstructorFromRERL(main, loc, 
								new ExpressionListRecResult(), (CStruct) underlyingFieldType);
					}	
				} else if (underlyingFieldType instanceof CNamed) {
					throw new AssertionError("This should not be the case as we took the underlying type.");
				} else {
					throw new UnsupportedSyntaxException(loc, "..");
				}	
			}
			newStmt.addAll(fieldContents.stmt);
			newDecl.addAll(fieldContents.decl);
			newAuxVars.putAll(fieldContents.auxVars);
			newOverappr.addAll(fieldContents.overappr);
			if (fieldContents.lrVal instanceof HeapLValue) {
				fieldValues.add(((HeapLValue) fieldContents.lrVal).getAddress());
			} else if (fieldContents.lrVal instanceof RValue) {
				fieldValues.add(((RValue) fieldContents.lrVal).getValue());
			} else {
				throw new AssertionError();
			}
		}
		final StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));

		final ExpressionResult result = new ExpressionResult(newStmt,
				new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
		return result;
	} 
}
