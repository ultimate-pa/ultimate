package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ConvExpr;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class InitializationHandler {

	FunctionHandler mFunctionHandler;

	StructHandler mStructHandler;

	MemoryHandler mMemoryHandler;	

	public InitializationHandler(
			FunctionHandler functionHandler, StructHandler structHandler,
			MemoryHandler memoryHandler) {
		super();
		this.mFunctionHandler = functionHandler;
		this.mStructHandler = structHandler;
		this.mMemoryHandler = memoryHandler;
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
	public ResultExpression initVar(ILocation loc, Dispatcher main,
			LeftHandSide lhs, CType cType, ResultExpression initializerRaw) {

		boolean onHeap = false;
		if (lhs != null && lhs instanceof VariableLHS) 
			onHeap = ((CHandler )main.cHandler).isHeapVar(((VariableLHS) lhs).getIdentifier());

		LRValue var = null;
		if (onHeap)
			var = new HeapLValue(new IdentifierExpression(loc, ((VariableLHS)lhs).getIdentifier()), cType);
		else
			var = lhs == null ? null : new LocalLValue(lhs, cType);

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
	private ResultExpression initVar(ILocation loc, Dispatcher main,
			CType cType, ResultExpression initializerRaw) {
		CType lCType = cType.getUnderlyingType();

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
		LRValue lrVal = null;

		//if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
		//carry over
		ResultExpression initializer = null;
		if (initializerRaw != null) {
			initializer = 
					initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			stmt.addAll(initializer.stmt);
			decl.addAll(initializer.decl);
			overappr.addAll(initializer.overappr);
			auxVars.putAll(initializer.auxVars);
		}

		VariableLHS lhs = null;

		Expression rhs = null;
		if (lCType instanceof CPrimitive) {
			switch (((CPrimitive) lCType).getGeneralType()) {
			case INTTYPE:
				if (initializer == null) {
					rhs = new IntegerLiteral(loc, SFO.NR0);
				} else {
					initializer = ConvExpr.rexBoolToIntIfNecessary(loc, initializer);
					rhs = initializer.lrVal.getValue();
				}
				break;
			case FLOATTYPE:
				if (initializer == null) {
					rhs = new RealLiteral(loc, SFO.NR0F);
				} else {
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
				rhs = new IdentifierExpression(loc, SFO.NULL);
			} else {
				CType initializerUnderlyingType = initializer.lrVal.cType.getUnderlyingType();
				if (initializerUnderlyingType instanceof CPointer
						|| initializerUnderlyingType instanceof CArray) {
					rhs = initializer.lrVal.getValue();
				} else if (initializerUnderlyingType instanceof CPrimitive 
						//						&& ((CPrimitive) initializerUnderlyingType).getType() == PRIMITIVE.INT){
						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == GENERALPRIMITIVE.INTTYPE){
					String offset = ((IntegerLiteral) initializer.lrVal.getValue()).getValue();
					if (offset.equals("0")) {
						rhs = new IdentifierExpression(loc, SFO.NULL);
					} else {
						rhs = MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc, "0"), 
								new IntegerLiteral(loc, offset), loc);
					}
				} else {
					throw new AssertionError("trying to initialize a pointer with something different from int and pointer");
				}
			}

			lrVal = new RValue(rhs, lCType);
		} else if (lCType instanceof CArray) {

			stmt.addAll(this.initBoogieArray(main, loc,
					initializer == null ? null : ((ResultExpressionListRec) initializer).list,
							lhs, (CArray) lCType));
			if (initializer == null) {
				stmt.addAll(this.initBoogieArray(main, loc,
						null, lhs, (CArray) lCType));
			} else if (initializer instanceof ResultExpressionListRec) {
				stmt.addAll(this.initBoogieArray(main, loc,
						((ResultExpressionListRec) initializer).list, lhs, (CArray) lCType));
			} else if (initializer instanceof ResultExpression) {// we have a variable length array and need the corresponding aux vars
				//					stmt.addAll(initializer.stmt);
				//					decl.addAll(initializer.decl);
				//					auxVars.putAll(initializer.auxVars);
			} else {
				assert false;
			}
			//			}
			assert lhs != null;
		} else if (lCType instanceof CStruct) {
			CStruct structType = (CStruct) lCType;

			ResultExpression scRex = this.makeStructConstructorFromRERL(main, loc, 
					(ResultExpressionListRec) initializer,
					structType);

			stmt.addAll(scRex.stmt);
			decl.addAll(scRex.decl);
			overappr.addAll(scRex.overappr);
			auxVars.putAll(scRex.auxVars);

			lrVal = new RValue(rhs, lCType);
		} else if (lCType instanceof CEnum) {
			if (initializer == null) {
				rhs = new IntegerLiteral(loc, SFO.NR0);
			} else {
				initializer = ConvExpr.rexBoolToIntIfNecessary(loc, initializer);
				rhs = initializer.lrVal.getValue();
			}		
			lrVal = new RValue(rhs, lCType);
		} else {
			String msg = "Unknown type - don't know how to initialize!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		assert (main.isAuxVarMapcomplete(decl, auxVars));

		// lrVal is null in case we got a lhs to assign to, the initializing value otherwise
		return new ResultExpression(stmt, lrVal, decl, auxVars, overappr);
	}

	/**
	 * Same as other initVar but with an LRValue as argument, not a LHS
	 * if var is a HeapLValue, something on Heap is initialized, 
	 * if it is a LocalLValue something off the Heap is initialized
	 */
	private ResultExpression initVar(ILocation loc, Dispatcher main,
			LRValue var, CType cType, ResultExpression initializerRaw) {
		assert var != null;

		boolean onHeap = var instanceof HeapLValue;

		CType lCType = cType.getUnderlyingType();

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();

		//if (f.i.) the initializer comes from a function call, it has statements and declarations that we need to
		//carry over
		ResultExpression initializer = null;
		if (initializerRaw != null) {
			initializer = 
					initializerRaw.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			stmt.addAll(initializer.stmt);
			decl.addAll(initializer.decl);
			overappr.addAll(initializer.overappr);
			auxVars.putAll(initializer.auxVars);
		}

		VariableLHS lhs = null;
		if (var instanceof LocalLValue)
			lhs = (VariableLHS) ((LocalLValue) var).getLHS();
		Expression rhs = null;
		if (lCType instanceof CPrimitive) {
			switch (((CPrimitive) lCType).getGeneralType()) {
			case INTTYPE:
				if (initializer == null) {
					rhs = new IntegerLiteral(loc, SFO.NR0);
				} else {
					initializer = ConvExpr.rexBoolToIntIfNecessary(loc, initializer);
					rhs = initializer.lrVal.getValue();
				}
				break;
			case FLOATTYPE:
				if (initializer == null) {
					rhs = new RealLiteral(loc, SFO.NR0F);
				} else {
					rhs = initializer.lrVal.getValue();
				}
				break;
			case VOID:
			default:
				throw new AssertionError("unknown type to init");
			}
			if (onHeap) {
				stmt.addAll(mMemoryHandler.getWriteCall(loc,
						(HeapLValue) var,
						new RValue(rhs, cType)));
			} else {
				assert lhs != null;
				stmt.add(new AssignmentStatement(loc, 
						new LeftHandSide[] { lhs },
						new Expression[] { rhs } ));
			}
		} else if (lCType instanceof CPointer) {
			if (initializer == null) {
				rhs = new IdentifierExpression(loc, SFO.NULL);
			} else {
				CType initializerUnderlyingType = initializer.lrVal.cType.getUnderlyingType();
				if (initializerUnderlyingType instanceof CPointer
						|| initializerUnderlyingType instanceof CArray) {
					rhs = initializer.lrVal.getValue();
				} else if (initializerUnderlyingType instanceof CPrimitive 
						&& ((CPrimitive) initializerUnderlyingType).getGeneralType() == GENERALPRIMITIVE.INTTYPE){
					String offset = ((IntegerLiteral) initializer.lrVal.getValue()).getValue();
					if (offset.equals("0")) {
						rhs = new IdentifierExpression(loc, SFO.NULL);
					} else {
						rhs = MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc, "0"), 
								new IntegerLiteral(loc, offset), loc);
					}
				} else {
					throw new AssertionError("trying to initialize a pointer with something different from int and pointer");
				}
			}
			if (onHeap) {
				stmt.addAll(mMemoryHandler.getWriteCall(loc, (HeapLValue) var, new RValue(rhs, lCType)));
			} else {
				assert lhs != null;
				stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
						new Expression[] { rhs } ));
			}
		} else if (lCType instanceof CArray) {

			if (onHeap) { 
				IdentifierExpression arrayAddress = (IdentifierExpression)((HeapLValue) var).getAddress();
				lhs = new VariableLHS(arrayAddress.getLocation(),
						arrayAddress.getIdentifier());			

				CallStatement mallocRex = mMemoryHandler.getMallocCall(main, mFunctionHandler,
						mMemoryHandler.calculateSizeOf(lCType, loc), new LocalLValue(lhs, cType), loc);
				stmt.add(mallocRex);

				if (initializer == null) {
					stmt.addAll(this.initArrayOnHeap(main, loc, 
							null, arrayAddress, (CArray) lCType));				
				} else if (initializer instanceof ResultExpressionListRec) {
					stmt.addAll(this.initArrayOnHeap(main, loc, 
							((ResultExpressionListRec) initializer).list, arrayAddress, (CArray) lCType));				
				} else if (initializer instanceof ResultExpression) {// we have a variable length array and need the corresponding aux vars
					//					stmt.addAll(initializer.stmt);
					//					decl.addAll(initializer.decl);
					//					auxVars.putAll(initializer.auxVars);
				} else {
					assert false;
				}

			} else { //not on Heap
				stmt.addAll(this.initBoogieArray(main, loc,
						initializer == null ? null : ((ResultExpressionListRec) initializer).list,
								lhs, (CArray) lCType));
				if (initializer == null) {
					stmt.addAll(this.initBoogieArray(main, loc,
							null, lhs, (CArray) lCType));
				} else if (initializer instanceof ResultExpressionListRec) {
					stmt.addAll(this.initBoogieArray(main, loc,
							((ResultExpressionListRec) initializer).list, lhs, (CArray) lCType));
				} else if (initializer instanceof ResultExpression) {// we have a variable length array and need the corresponding aux vars
					//					stmt.addAll(initializer.stmt);
					//					decl.addAll(initializer.decl);
					//					auxVars.putAll(initializer.auxVars);
				} else {
					assert false;
				}
			}
			assert lhs != null;
		} else if (lCType instanceof CStruct) {
			CStruct structType = (CStruct) lCType;

			if (onHeap) {
				assert var != null;
				ResultExpression heapWrites = this.initStructOnHeapFromRERL(main, loc, 
						((HeapLValue) var).getAddress(),
						(ResultExpressionListRec) initializer,
						structType);

				stmt.addAll(heapWrites.stmt);
				decl.addAll(heapWrites.decl);
				overappr.addAll(heapWrites.overappr);
				auxVars.putAll(heapWrites.auxVars);
			} else {
				ResultExpression scRex = this.makeStructConstructorFromRERL(main, loc, 
						(ResultExpressionListRec) initializer,
						structType);

				stmt.addAll(scRex.stmt);
				decl.addAll(scRex.decl);
				overappr.addAll(scRex.overappr);
				auxVars.putAll(scRex.auxVars);

				assert lhs != null;
				stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { scRex.lrVal.getValue() }));
			}
		} else if (lCType instanceof CEnum) {
			if (initializer == null) {
				rhs = new IntegerLiteral(loc, SFO.NR0);
			} else {
				initializer = ConvExpr.rexBoolToIntIfNecessary(loc, initializer);
				rhs = initializer.lrVal.getValue();
			}		
			if (onHeap) {
				stmt.addAll(mMemoryHandler.getWriteCall(loc,
						(HeapLValue) var,
						new RValue(rhs, cType)));
			} else {
				assert lhs != null;
				stmt.add(new AssignmentStatement(loc, 
						new LeftHandSide[] { lhs },
						new Expression[] { rhs } ));
			}
		} else {
			String msg = "Unknown type - don't know how to initialize!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		assert (main.isAuxVarMapcomplete(decl, auxVars));

		return new ResultExpression(stmt, null, decl, auxVars, overappr);
	}

	/**
	 * Initializes an array that lies on heap, either with some given values or to its default values.
	 * @param list The values that the array should be initialized with, null for default init
	 * @param startAddress The address on the heap that the array starts at
	 * @param arrayType The type of the array (containing its size and value type)
	 * @return a list of statements that do the initialization
	 */
	private ArrayList<Statement> initArrayOnHeap(Dispatcher main, ILocation loc, 
			ArrayList<ResultExpressionListRec> list, Expression startAddress,
			CArray arrayType) {
		ArrayList<Statement> arrayWrites = new ArrayList<Statement>();

		Expression sizeOfCell = mMemoryHandler.calculateSizeOf(arrayType.getValueType(), loc); 
		Expression[] dimensions = arrayType.getDimensions();
		Integer currentSizeInt = null;
		try {
			currentSizeInt = Integer.parseInt(((IntegerLiteral) dimensions[0]).getValue());
		} catch (NumberFormatException nfe) {
			throw new UnsupportedSyntaxException(loc, "trying to initialize an array whose size we don't know");
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

		if (dimensions.length == 1) {
			RValue val = null;

			for (int i = 0; i < currentSizeInt; i++) {
				CType valueType = arrayType.getValueType().getUnderlyingType();
				//TODO: we may need to pass statements, decls, ...
				if (list != null && list.size() > i && list.get(i).lrVal != null) {
					val = (RValue) list.get(i).lrVal; 
				} else {
					if (valueType instanceof CArray) {
						throw new AssertionError("this should not be the case as we are in the inner/outermost array right??");
					} else if  (valueType instanceof CStruct) {
						ResultExpression sInit = this.initStructOnHeapFromRERL(main, loc, 
								null, null, (CStruct) valueType);
						arrayWrites.addAll(sInit.stmt);
						assert sInit.decl.size() == 0 && sInit.auxVars.size() == 0 : "==> change return type of initArray..";
						val = (RValue) sInit.lrVal;
					} else if (valueType instanceof CPrimitive 
							|| valueType instanceof CPointer) {
						val = (RValue) (main.cHandler.getInitHandler().initVar(loc, main, 
								(VariableLHS) null, valueType, null)).lrVal;
					} else {
						throw new UnsupportedSyntaxException(loc, "trying to init unknown type");
					}
				}

				Expression writeOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
						new IntegerLiteral(null, new Integer(i).toString()), 
						sizeOfCell,
						null);	
				writeOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus,
						newStartAddressOffset,
						writeOffset, 
						loc);

				Expression writeLocation = MemoryHandler.constructPointerFromBaseAndOffset(
						newStartAddressBase,
						writeOffset, 
						loc);

				arrayWrites.addAll(mMemoryHandler.getWriteCall(loc, new HeapLValue(writeLocation, valueType), val));
			}
		} else {
			for (int i = 0; i < currentSizeInt; i++) { 
				Expression newStartAddressOffsetInner = newStartAddressOffset;

				Expression blockOffset = sizeOfCell;
				for (int j = 1; j < dimensions.length; j++) {
					blockOffset = 
							CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
									dimensions[j],
									blockOffset,
									loc);
				}
				blockOffset = 
						CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
								new IntegerLiteral(loc, new Integer(i).toString()),	blockOffset,
								loc);	
				newStartAddressOffsetInner = 
						CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus,
								newStartAddressOffsetInner,
								blockOffset,
								loc);	

				ArrayList<Expression> innerDims = new ArrayList<Expression>(Arrays.asList(arrayType.getDimensions()));
				innerDims.remove(0);//TODO ??
				CArray innerArrayType = new CArray(innerDims.toArray(new Expression[0]), 
						arrayType.getValueType());

				arrayWrites.addAll(
						initArrayOnHeap(main, 
								loc, 
								list != null ? list.get(i).list : null,
										MemoryHandler.constructPointerFromBaseAndOffset(
												newStartAddressBase,
												newStartAddressOffsetInner, 
												loc),
												innerArrayType)); 
			}
		}
		return arrayWrites;
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
	private ArrayList<Statement> initBoogieArray(Dispatcher main, ILocation loc, 
			ArrayList<ResultExpressionListRec> list, LeftHandSide innerArrayAccessLHS,
			CArray arrayType) {
		ArrayList<Statement> arrayWrites = new ArrayList<Statement>();

		Expression[] dimensions = arrayType.getDimensions();
		Integer currentSizeInt = null;
		try {
			currentSizeInt = Integer.parseInt(((IntegerLiteral) dimensions[0]).getValue());
		} catch (NumberFormatException nfe) {
			throw new UnsupportedSyntaxException(loc, "trying to initialize an array whose size we don't know");
		}

		if (dimensions.length == 1) {
			RValue val = null;

			for (int i = 0; i < currentSizeInt; i++) {
				//TODO: we may need to pass statements, decls, ...
				if (list != null && list.size() > i && list.get(i).lrVal != null) {
					val = (RValue) list.get(i).lrVal; //if not enough values are given, fill the rest with the last --> wrong? FIXME
				} else {
					CType valueType = arrayType.getValueType().getUnderlyingType();

					if (valueType instanceof CArray) {
						throw new AssertionError("this should not be the case as we are in the inner/outermost array right??");
					} else if  (valueType instanceof CStruct) {
						ResultExpression sInit = this.makeStructConstructorFromRERL(main, loc, 
								null, (CStruct) valueType);
						arrayWrites.addAll(sInit.stmt);
						assert sInit.decl.size() == 0 && sInit.auxVars.size() == 0 : "==> change return type of initArray..";
						val = (RValue) sInit.lrVal;
					} else if (valueType instanceof CPrimitive 
							|| valueType instanceof CPointer) {
						val = (RValue) (main.cHandler.getInitHandler().initVar(loc, main, 
								(VariableLHS) null, valueType, null)).lrVal;
					} else {
						throw new UnsupportedSyntaxException(loc, "trying to init unknown type");
					}
				}
				Expression[] newIndices = null;
				LeftHandSide newLHS = null;
				if (innerArrayAccessLHS instanceof ArrayLHS) {
					ArrayList<Expression> innerIndices = 
							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
					innerIndices.add(new IntegerLiteral(loc, new Integer(i).toString()));
					newIndices = innerIndices.toArray(new Expression[0]);
					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
				} else {
					newIndices = new Expression[] { new IntegerLiteral(loc, new Integer(i).toString()) };
					newLHS = innerArrayAccessLHS;
				}

				ArrayLHS arrayAccessLHS = new ArrayLHS(loc, newLHS, newIndices);
				arrayWrites.add(new AssignmentStatement(loc, 
						new LeftHandSide[] { arrayAccessLHS }, new Expression[] { val.getValue() }));
			}
		} else {
			for (int i = 0; i < currentSizeInt; i++) { 

				Expression[] newIndices = null;
				LeftHandSide newLHS = null;
				if (innerArrayAccessLHS instanceof ArrayLHS) {
					ArrayList<Expression> innerIndices = 
							new ArrayList<Expression>(Arrays.asList(((ArrayLHS) innerArrayAccessLHS).getIndices()));
					innerIndices.add(new IntegerLiteral(loc, new Integer(i).toString()));
					newIndices = innerIndices.toArray(new Expression[0]);
					newLHS = ((ArrayLHS) innerArrayAccessLHS).getArray();
				} else { 
					newIndices = new Expression[] { new IntegerLiteral(loc, new Integer(i).toString()) };
					newLHS = innerArrayAccessLHS;
				}

				ArrayList<Expression> innerDims = new ArrayList<Expression>(Arrays.asList(arrayType.getDimensions()));
				innerDims.remove(0);//TODO ??
				CArray innerArrayType = new CArray(innerDims.toArray(new Expression[0]), 
						arrayType.getValueType());

				arrayWrites.addAll(
						initBoogieArray(main, 
								loc,
								list != null ? list.get(i).list : null,
										new ArrayLHS(loc, newLHS, newIndices), innerArrayType)); 
			}
		}
		return arrayWrites;
	}

	/**
	 * Generate the write calls for the initialization of the struct onHeap.
	 */
	private ResultExpression initStructOnHeapFromRERL(Dispatcher main, ILocation loc, 
			Expression startAddress, 
			ResultExpressionListRec rerlIn, CStruct structType) {
		ResultExpressionListRec rerl = null;
		if (rerlIn == null)
			rerl = new ResultExpressionListRec();
		else
			rerl = rerlIn;

		if (rerl.lrVal != null) {//we have an identifier (or sth else too?)
			ResultExpression writes = new ResultExpression((RValue) null);
			ArrayList<Statement> writeCalls = mMemoryHandler.getWriteCall(loc,
					new HeapLValue(startAddress, rerl.lrVal.cType), (RValue) rerl.lrVal);
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
		ArrayList<Statement> newStmt = new ArrayList<Statement>();
		ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> newAuxVars =
				new LinkedHashMap<VariableDeclaration, ILocation>();
		List<Overapprox> newOverappr = new ArrayList<Overapprox>();

		String[] fieldIds = structType.getFieldIds();
		CType[] fieldTypes = structType.getFieldTypes();

		boolean isUnion = (structType instanceof CUnion);
		//in a union, only one field of the underlying struct may be initialized
		//we do the first, if no fieldname is given, this variable stores whether
		//we already initialized a field
		boolean unionAlreadyInitialized = false;

		for (int i = 0; i < fieldIds.length; i++) {
			CType underlyingFieldType = fieldTypes[i].getUnderlyingType();

			Expression fieldAddressBase = newStartAddressBase;
			Expression fieldAddressOffset = mStructHandler.computeStructFieldOffset(mMemoryHandler, loc, fieldIds[i], 
					newStartAddressOffset, structType);
			StructConstructor fieldPointer = MemoryHandler.constructPointerFromBaseAndOffset(
					fieldAddressBase, fieldAddressOffset, loc);
			HeapLValue fieldHlv = new HeapLValue(fieldPointer, underlyingFieldType);

			ResultExpression fieldWrites = null; 

			if (isUnion) {
				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
				//TODO: maybe not use auxiliary variables so lavishly
				if (!unionAlreadyInitialized
						&& rerl.list.size() == 1 
						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
						|| fieldIds[i].equals(rerl.list.get(0).field))
						&& (underlyingFieldType instanceof CStruct
								|| rerl.list.get(0).lrVal.cType.equals(underlyingFieldType))) {
					//use the value from the rerl to initialize the union
					fieldWrites = main.cHandler.getInitHandler().initVar(loc, main, 
							fieldHlv,
							underlyingFieldType, rerl.list.get(0)
							);
					unionAlreadyInitialized = true;
				} else {
					//fill in the uninitialized aux variable
					String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.UNION);

					fieldWrites = new ResultExpression((RValue) null);
					fieldWrites.stmt.addAll(mMemoryHandler.getWriteCall(loc,
							fieldHlv,
							new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType)));
					VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0], 
							new VarList[] { new VarList(loc, new String[] { tmpId }, 
									main.typeHandler.ctype2asttype(loc, underlyingFieldType)) } );
					fieldWrites.decl.add(auxVarDec);
					fieldWrites.auxVars.put(auxVarDec, loc);
				}

			} else {
				if(underlyingFieldType instanceof CPrimitive) {
					fieldWrites = main.cHandler.getInitHandler().initVar(loc, main, 
							fieldHlv, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CPointer) {
					fieldWrites = main.cHandler.getInitHandler().initVar(loc, main, 
							fieldHlv, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CArray) {
					ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
					ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
					Map<VariableDeclaration, ILocation> fieldAuxVars =
							new LinkedHashMap<VariableDeclaration, ILocation>();

					ResultExpressionListRec arrayInitRerl = null;
					if (i < rerl.list.size())
						arrayInitRerl = rerl.list.get(i);

					fieldStmt.addAll(this.initArrayOnHeap(main, loc, 
							arrayInitRerl == null ? null : arrayInitRerl.list, 
									fieldPointer,
									 (CArray) underlyingFieldType));

					fieldWrites = new ResultExpression(fieldStmt, 
							null,
							fieldDecl, fieldAuxVars);
				} else if (underlyingFieldType instanceof CEnum) {
					//like CPrimitive (?)
					fieldWrites = main.cHandler.getInitHandler().initVar(loc, main, 
							fieldHlv, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
//					throw new UnsupportedSyntaxException(loc, "..");
				} else if (underlyingFieldType instanceof CStruct) {
					ResultExpressionListRec fieldRerl = i < rerl.list.size() ? 
							rerl.list.get(i) : new ResultExpressionListRec();
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
		ResultExpression result = new ResultExpression(newStmt,
				null, newDecl, newAuxVars, newOverappr);
		return result;
	} 

	/**
	 * Takes a ResultExpressionListRec and a CStruct(type) and generates a StructConstructor with the 
	 * nesting structure from the CStruct and the values from the RERL.
	 * If the RERL is null, the default initialization (int: 0, Ptr: NULL, ...) is used for each entry.
	 */
	private ResultExpression makeStructConstructorFromRERL(Dispatcher main, ILocation loc, 
			ResultExpressionListRec rerlIn, CStruct structType) {
		ResultExpressionListRec rerl = null;
		if (rerlIn == null)
			rerl = new ResultExpressionListRec();
		else
			rerl = rerlIn;

		if (rerl.lrVal != null) //we have an identifier (or sth else too?)
			return new ResultExpression(rerl.stmt, rerl.lrVal, rerl.decl,
					rerl.auxVars, rerl.overappr);

		boolean isUnion = (structType instanceof CUnion);
		//in a union, only one field of the underlying struct may be initialized
		//we do the first, if no fieldname is given, this variable stores whether
		//we already initialized a field
		boolean unionAlreadyInitialized = false;

		//everything for the new Result
		ArrayList<Statement> newStmt = new ArrayList<Statement>();
		ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> newAuxVars =
				new LinkedHashMap<VariableDeclaration, ILocation>();
		List<Overapprox> newOverappr = new ArrayList<Overapprox>();

		String[] fieldIds = structType.getFieldIds();
		CType[] fieldTypes = structType.getFieldTypes();

		//the new Arrays for the StructConstructor
		ArrayList<String> fieldIdentifiers = new ArrayList<String>();
		ArrayList<Expression> fieldValues = new ArrayList<Expression>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			CType underlyingFieldType = fieldTypes[i].getUnderlyingType();

			ResultExpression fieldContents = null; 

			if (isUnion) {
				assert rerl.list.size() == 0 || rerl.list.size() == 1 : "union initializers must have only one field";
				//TODO: maybe not use auxiliary variables so lavishly
				String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.UNION);
				if (!unionAlreadyInitialized
						&& rerl.list.size() == 1 
						&& (rerl.list.get(0).field == null || rerl.list.get(0).field.equals("")
						|| fieldIds[i].equals(rerl.list.get(0).field))
						&& (underlyingFieldType instanceof CStruct
								|| rerl.list.get(0).lrVal.cType.equals(underlyingFieldType))) {
					//use the value from the rerl to initialize the union
					fieldContents = main.cHandler.getInitHandler().initVar(loc, main, 
							new VariableLHS(loc, tmpId),
							underlyingFieldType, rerl.list.get(0));
					fieldContents.lrVal = new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType);
					unionAlreadyInitialized = true;
				} else {
					//fill in the uninitialized aux variable
					fieldContents = new ResultExpression(
							new RValue(new IdentifierExpression(loc, tmpId), underlyingFieldType));
				}
				VariableDeclaration auxVarDec = new VariableDeclaration(loc, new Attribute[0], 
						new VarList[] { new VarList(loc, new String[] { tmpId }, 
								main.typeHandler.ctype2asttype(loc, underlyingFieldType)) } );
				fieldContents.decl.add(auxVarDec);
				fieldContents.auxVars.put(auxVarDec, loc);
			} else {
				if(underlyingFieldType instanceof CPrimitive) {
					fieldContents = main.cHandler.getInitHandler().initVar(loc, main, 
							(VariableLHS) null, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CPointer) {
					fieldContents = main.cHandler.getInitHandler().initVar(loc, main, 
							(VariableLHS) null, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CArray) {
					ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
					ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
					Map<VariableDeclaration, ILocation> fieldAuxVars =
							new LinkedHashMap<VariableDeclaration, ILocation>();

					String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT);

					ResultExpressionListRec arrayInitRerl = null;
					if (i < rerl.list.size())
						arrayInitRerl = rerl.list.get(i);

					Expression fieldEx = new IdentifierExpression(loc, tmpId);
					RValue lrVal = new RValue(fieldEx, underlyingFieldType);

					VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, 
							main.typeHandler.ctype2asttype(loc, underlyingFieldType),
							loc);
					fieldAuxVars.put(tVarDecl, (CACSLLocation) loc);
					fieldDecl.add(tVarDecl);
					VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
					fieldStmt.addAll(main.cHandler.getInitHandler().initBoogieArray(main, loc, 
							arrayInitRerl == null ? null : arrayInitRerl.list, 
									fieldLHS, (CArray) underlyingFieldType));

					fieldContents = new ResultExpression(fieldStmt, lrVal, fieldDecl, fieldAuxVars);
				} else if (underlyingFieldType instanceof CEnum) {
					//like CPrimitive
					fieldContents = main.cHandler.getInitHandler().initVar(loc, main, 
							(VariableLHS) null, underlyingFieldType, 
							i < rerl.list.size() ? rerl.list.get(i) : null);
				} else if (underlyingFieldType instanceof CStruct) {
					if (i < rerl.list.size())
						fieldContents = makeStructConstructorFromRERL(main, loc,
								rerl.list.get(i), (CStruct) underlyingFieldType);
					else
						fieldContents = makeStructConstructorFromRERL(main, loc, 
								new ResultExpressionListRec(), (CStruct) underlyingFieldType);	
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
			assert fieldContents.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
			fieldValues.add(((RValue) fieldContents.lrVal).getValue());
		}
		StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));

		ResultExpression result = new ResultExpression(newStmt,
				new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
		return result;
	} 
}
