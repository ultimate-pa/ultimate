/**
 * Describing a translation result for expressions.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class ResultExpression extends Result {
	/**
	 * Statement list.
	 */
	public final ArrayList<Statement> stmt;
//	/**
//	 * The expression.
//	 */
//	public Expression expr;
	/**
	 * the LRValue may contain the contents of a memory cell or its address or both
	 */
	public LRValue lrVal;
	/**
	 * Declaration list. Some translations need to declare some temporary
	 * variables, which we do here.
	 */
	public final ArrayList<Declaration> decl;
	/**
	 * A description of the C variable.
	 */
	public final ArrayList<CType> declCTypes;
	/**
	 * The description of the C type of this expression.
	 */
	public CType cType;
	
	/**
	 * Auxiliary variables occurring in this result. The variable declaration
	 * of the var is mapped to the exact location for that it was constructed.
	 */
	public final Map<VariableDeclaration, CACSLLocation> auxVars;

	/**
	 * Constructor.
	 * 
	 * @param stmt
	 *            the statement list to hold
	 * @param expr
	 *            the expression list to hold
	 * @param decl
	 *            the declaration list to hold
	 */
	public ResultExpression(ArrayList<Statement> stmt, //Expression expr,
			LRValue lrVal,
			ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars) {
		super(null);
		this.stmt = stmt;
//		this.expr = expr;
		this.lrVal = lrVal;
		this.decl = decl;
		this.declCTypes = new ArrayList<CType>();
		this.auxVars = auxVars;
	}
	/**
	 * Constructor.
	 * 
	 * @param stmt
	 *            the statement list to hold
	 * @param expr
	 *            the expression list to hold
	 * @param decl
	 *            the declaration list to hold
	 */
	public ResultExpression(ArrayList<Statement> stmt, //Expression expr,
			LRValue lrVal,
			ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars, CType cType) {
		super(null);
		this.stmt = stmt;
//		this.expr = expr;
		this.lrVal = lrVal;
		this.decl = decl;
		this.declCTypes = new ArrayList<CType>();
		this.auxVars = auxVars;
		this.cType = cType;
	}
	
	/**
	 * Constructor for only one element
	 * 
	 * @param expr
	 *            the expression to add
	 */
	public ResultExpression(//Expression expr,
			LRValue lrVal,
			Map<VariableDeclaration, CACSLLocation> auxVars) {
		super(null);
		this.stmt = new ArrayList<Statement>();
//		this.expr = expr;
		this.lrVal = lrVal;
		this.decl = new ArrayList<Declaration>();
		this.declCTypes = new ArrayList<CType>();
		this.auxVars = auxVars;
	}
	
	public ResultExpression(
			LRValue lrVal,
			CType cType) {
		super(null);
		this.stmt = new ArrayList<Statement>();
		this.lrVal = lrVal;
		this.cType = cType;
		this.decl = new ArrayList<Declaration>();
		this.declCTypes = new ArrayList<CType>();
		this.auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
	}
		
	public ResultExpression switchToRValue(Dispatcher main, MemoryHandler memoryHandler, 
			StructHandler structHandler, CACSLLocation loc) {
		ResultExpression rex = null;
		if (lrVal == null)
			return this;
		else if (lrVal instanceof RValue)
			return this;
		else if (lrVal instanceof LocalLValue) {
			rex = new ResultExpression(
					this.stmt, new RValue(((LocalLValue) lrVal).getValue()), this.decl, this.auxVars, this.cType);
			return rex;
		} else {
			HeapLValue hlv = (HeapLValue) lrVal;
//			SymbolTable sT = ((MainDispatcher) main).cHandler.getSymbolTable();
//			Expression value = hlv.getAddress();
			
			//retain already created stmt, decl, auxVars
			ArrayList<Statement> newStmt = new ArrayList<Statement>(this.stmt);
			ArrayList<Declaration> newDecl = new ArrayList<Declaration>(this.decl);
			HashMap<VariableDeclaration, CACSLLocation> newAuxVars = 
					new HashMap<VariableDeclaration, CACSLLocation>(this.auxVars); 
			RValue newValue = null;
			
			InferredType heapReadType = null;
			
			CType underlyingType = this.cType instanceof CNamed ? 
					((CNamed) this.cType).getUnderlyingType() :
						this.cType;
			
			if (underlyingType instanceof CPrimitive) {
				CPrimitive cp = (CPrimitive) this.cType;
				ResultExpression readResult;
				switch (cp.getType()) {
				case INT:
					heapReadType = new InferredType(Type.Integer);
					rex = memoryHandler.getReadCall(
							main, heapReadType, hlv.getAddress(), new CPointer(this.cType));
					newStmt.addAll(rex.stmt);
					newDecl.addAll(rex.decl);
					newAuxVars.putAll(rex.auxVars);	
					newValue = (RValue) rex.lrVal;
					break;
				case BOOL:
				case CHAR:
				default:
					throw new UnsupportedSyntaxException("..");
				}
			} else if (underlyingType instanceof CPointer) {
				heapReadType = new InferredType(Type.Pointer);
				rex = memoryHandler.getReadCall(
						main, heapReadType, hlv.getAddress(), new CPointer(this.cType));
				newStmt.addAll(rex.stmt);
				newDecl.addAll(rex.decl);
				newAuxVars.putAll(rex.auxVars);	
				newValue = (RValue) rex.lrVal;
			} else if (underlyingType instanceof CArray) {
			} else if (underlyingType instanceof CEnum) {
			} else if (underlyingType instanceof CStruct) {
				CStruct structType = (CStruct) underlyingType;
				rex = readStructFromHeap(main, structHandler, memoryHandler, loc, 
						hlv.getAddress(), structType);
				newStmt.addAll(rex.stmt);
				newDecl.addAll(rex.decl);
				newAuxVars.putAll(rex.auxVars);	
				newValue = (RValue) rex.lrVal;	
			} else if (underlyingType instanceof CNamed) {
				assert false : "This should not be the case as we took the underlying type.";
			} else {
				throw new UnsupportedSyntaxException("..");
			}
			rex = new ResultExpression(newStmt, newValue, newDecl, newAuxVars, rex.cType);
			return rex;
		}
	}
	
	/**
	 * Read the contents of a struct (given as a pointer) from the heap recursively (for nested structs)
	 * returning a StructConstructor.
	 * @param main
	 * @param structHandler
	 * @param memoryHandler
	 * @param loc
	 * @param structOnHeapAddress
	 * @param structType
	 * @return A result whose value is a StructConstructor and whose statements make the necessary calls to
	 * fill the items inside the StructConstructor correctly
	 */
	ResultExpression readStructFromHeap(Dispatcher main, 
			StructHandler structHandler, MemoryHandler memoryHandler, CACSLLocation loc,
			Expression structOnHeapAddress, CStruct structType) {
		ResultExpression result = null;
		
		Expression currentStructBaseAddress = getPointerBaseAddress(structOnHeapAddress, loc);
		Expression currentStructOffset = getPointerOffset(structOnHeapAddress, loc);
		
		//everything for the new Result
		ArrayList<Statement> newStmt = new ArrayList<Statement>();
		ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		HashMap<VariableDeclaration, CACSLLocation> newAuxVars = new HashMap<VariableDeclaration, CACSLLocation>();

		String[] fieldIds = structType.getFieldIds();
		CType[] fieldTypes = structType.getFieldTypes();

		//the new Arrays for the StructConstructor
		ArrayList<String> fieldIdentifiers = new ArrayList<String>();
		ArrayList<Expression> fieldValues = new ArrayList<Expression>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);
		
			CType underlyingType;
			if (fieldTypes[i] instanceof CNamed)
				underlyingType = ((CNamed) fieldTypes[i]).getUnderlyingType();
			else
				underlyingType = fieldTypes[i];
			
			ResultExpression fieldRead = null; 
			if(underlyingType instanceof CPrimitive) {
				InferredType typeOnHeap = null;
				CPrimitive cp = (CPrimitive) fieldTypes[i];
				switch (cp.getType()) {
				case INT:
					typeOnHeap = new InferredType(Type.Integer);
					break;
//				case POINTER:						
//					typeOnHeap = new InferredType(Type.Pointer);
//					break;
				case BOOL:
					throw new UnsupportedSyntaxException("..");
//					break;
				case CHAR:
					throw new UnsupportedSyntaxException("..");
//					break;
				default:
					throw new UnsupportedSyntaxException("..");
				}
				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
								main, memoryHandler, loc, fieldIds[i], typeOnHeap,
								structOnHeapAddress, //fieldTypes[i]);//TODO: or take the underlying type??
								structType);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CPointer) {
				InferredType typeOnHeap = new InferredType(Type.Integer);
				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], typeOnHeap,
						structOnHeapAddress, //fieldTypes[i]);//TODO: or take the underlying type??
						structType);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CArray) {
					throw new UnsupportedSyntaxException("..");
			} else if (underlyingType instanceof CEnum) {
					throw new UnsupportedSyntaxException("..");
			} else if (underlyingType instanceof CStruct) {
				//sae = {base: currentStructBaseAddress, offset: currentStructOffset + thisFieldOffset }
				Expression innerStructOffset = 
						structHandler.getStructOffsetConstantExpression(loc, fieldIds[i], underlyingType);
				Expression innerStructAddress = constructPointerFromBaseAndOffset(currentStructBaseAddress, 
						new BinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, 
								currentStructOffset, 
								innerStructOffset),
						loc);
				
				fieldRead = readStructFromHeap(main, structHandler, memoryHandler, 
						loc, innerStructAddress, (CStruct) underlyingType);
				
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CNamed) {
				assert false : "This should not be the case as we took the underlying type.";
			} else {
				throw new UnsupportedSyntaxException("..");
			}	
			

			assert fieldRead.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
			fieldValues.add(((RValue) fieldRead.lrVal).getValue());

		}
		StructConstructor sc = new StructConstructor(loc, 
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));
		
		result = new ResultExpression(newStmt, new RValue(sc), newDecl, newAuxVars);
		result.cType = structType;

		return result;
	}
	
	
	public static StructAccessExpression getPointerBaseAddress(Expression pointer, CACSLLocation loc) {
		return new StructAccessExpression(loc, new InferredType(Type.Integer), pointer, "base");
	}
	
	public static StructAccessExpression getPointerOffset(Expression pointer, CACSLLocation loc) {
		return new StructAccessExpression(loc, new InferredType(Type.Integer), pointer, "offset");
	}
	
	public static StructConstructor constructPointerFromBaseAndOffset(Expression base, Expression offset, CACSLLocation loc) {
		return new StructConstructor(loc, new InferredType(Type.Pointer), 
				new String[]{"base", "offset"}, new Expression[]{base, offset});
	}
	//	InferredType getHeapTypeFromCType(CType ct) {
	//		InferredType it = null;
	//		
	//		CType underlyingType = ((CNamed) this.cType).getUnderlyingType();
	//		
	//		if (underlyingType instanceof CPrimitive) {
	//			CPrimitive cp = (CPrimitive) this.cType;
	//			ResultExpression readResult;
	//			switch (cp.getType()) {
	//			case INT:
	//				return new InferredType(Type.Integer);
	//				break;
	//			case POINTER:						
	//	
	//				break;
	//			case BOOL:
	//				break;
	//			case CHAR:
	//				break;
	//			default:
	//				throw new UnsupportedSyntaxException("..");
	//			}
	//		} else if (underlyingType instanceof CPointer) {
	//		} else if (underlyingType instanceof CArray) {
	//		} else if (underlyingType instanceof CEnum) {
	//		} else if (underlyingType instanceof CStruct) {
	//				return new InferredType(Type.Pointer);
	//		} else if (underlyingType instanceof CNamed) {
	//			assert false : "This should not be the case as we took the underlying type.";
	//		} else {
	//			throw new UnsupportedSyntaxException("..");
	//		}	
//	}
//	public ResultExpression switchToLHS(Dispatcher main, MemoryHandler memoryHandler) {
//		assert !(lrVal instanceof RValue);
//		
//		if (lrVal instanceof LocalLValue) {
//			return this;
//		} else {
//			HeapLValue hlv = (HeapLValue) lrVal;
//			assert !hlv.addressIsValue : "we cannot write into an address (right? without casts..?)";
//			
//			write = memoryHandler.getWriteCall(hlv.address, val)
//		}
//		return null;
//	}
}
