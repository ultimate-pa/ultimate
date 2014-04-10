/**
 * Describing a translation result for expressions.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

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
//	public final ArrayList<CType> declCTypes;
//	/**
//	 * The description of the C type of this expression.
//	 */
//	public CType cType; //--> moved to LRValue

	/**
	 * A list of overapproximation flags.
	 */
	public final List<Overapprox> overappr;

	/**
	 * Auxiliary variables occurring in this result. The variable declaration
	 * of the var is mapped to the exact location for that it was constructed.
	 */
	public final Map<VariableDeclaration, ILocation> auxVars;
	
	
	/**
	 * especially for the havocs when writign a union.
	 * contains the field that must be havoced if this union
	 * is written.
	 */
	public final Map<StructLHS, CType> unionFieldIdToCType;
	
	/**
	 * Use this to lock this ResultExpression. If the ResultExpression is locked
	 * its fields should not obtain new elements any more.
	 * (alex:) The purpose is that once we have read those fields --> and added them to another
	 * ResultExpression <-- we want to be sure that they are not changed anymore in this,
	 * as then the other expression might contain too few/many entries in these fields.
	 * TODO: implement this consequently, make fields private
	 */
	private boolean m_Locked = false;
	
	/**
	 * Lock this ResultExpression after usage to forbid that someone switches
	 * to RValue.
	 */
	public void lock() {
		m_Locked = true;
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
     * @param overapproxList
     *            list of overapproximation flags
     */
    public ResultExpression(ArrayList<Statement> stmt, //Expression expr,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overapproxList,
            Map<StructLHS, CType> uField2CType) {
        super(null);
        this.stmt = stmt;
        //      this.expr = expr;
        this.lrVal = lrVal;
        this.decl = decl;
//        this.declCTypes = new ArrayList<CType>();
        this.auxVars = auxVars;
        this.overappr = overapproxList;
        this.unionFieldIdToCType = uField2CType;
    }
    
    
    public ResultExpression(ArrayList<Statement> stmt, //Expression expr,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overapproxList) {
    	this(stmt, lrVal, decl, auxVars, overapproxList, null);
    }
    
    public ResultExpression(ArrayList<Statement> stmt, //Expression expr,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars) {
        this(stmt, lrVal, decl,
                auxVars, new ArrayList<Overapprox>(), null);
    }

	public ResultExpression(//Expression expr,
			LRValue lrVal,
			Map<VariableDeclaration, ILocation> auxVars,
			List<Overapprox> overapproxList) {
	    this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(),
	            auxVars, overapproxList, null);
		//		this.expr = expr;
	}
	
	public ResultExpression(//Expression expr,
            LRValue lrVal,
            Map<VariableDeclaration, ILocation> auxVars) {
        this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(),
                auxVars);
        //      this.expr = expr;
    }

    public ResultExpression(
            LRValue lrVal) {
        this(lrVal, new LinkedHashMap<VariableDeclaration, ILocation>());
    }
    
    /**
     * copy constructor
     */
    public ResultExpression(ResultExpression rex) {
    	super(null);
    	this.stmt = rex.stmt;
    	this.lrVal = rex.lrVal;
    	this.decl = rex.decl;
    	this.auxVars = rex.auxVars;
    	this.overappr = rex.overappr;
    	this.unionFieldIdToCType = rex.unionFieldIdToCType;
    }

	public ResultExpression switchToRValueIfNecessary(Dispatcher main, MemoryHandler memoryHandler, 
			StructHandler structHandler, ILocation loc) {

		if (lrVal == null)
			return this;
		else if (lrVal instanceof RValue)
			return this;
		else if (lrVal instanceof LocalLValue) {
			RValue newRVal = new RValue(((LocalLValue) lrVal).getValue(),
					        lrVal.cType, lrVal.isBoogieBool);
//					        lrVal.cType, lrVal.isWrappedBool, lrVal.isPointer, lrVal.isOnHeap);
			return new ResultExpression(
					this.stmt, newRVal, this.decl, this.auxVars,
					        this.overappr, this.unionFieldIdToCType);
		} else {
			if (m_Locked) {
				throw new AssertionError("this ResultExpression is already locked");
			}
			ResultExpression rex = null;
			HeapLValue hlv = (HeapLValue) lrVal;
			//			SymbolTable sT = ((MainDispatcher) main).cHandler.getSymbolTable();
			//			Expression value = hlv.getAddress();

			//retain already created stmt, decl, auxVars
			ArrayList<Statement> newStmt = new ArrayList<Statement>(this.stmt);
			ArrayList<Declaration> newDecl = new ArrayList<Declaration>(this.decl);
			LinkedHashMap<VariableDeclaration, ILocation> newAuxVars = 
					new LinkedHashMap<VariableDeclaration, ILocation>(this.auxVars); 
			RValue newValue = null;

//			InferredType heapReadType = null;

			CType underlyingType = this.lrVal.cType instanceof CNamed ? 
					((CNamed) this.lrVal.cType).getUnderlyingType() :
						this.lrVal.cType;

//					RValue addressRVal = new RValue(hlv.getAddress(), new CPointer(this.lrVal.cType),
					RValue addressRVal = new RValue(hlv.getAddress(), this.lrVal.cType, //has the type of what lies at that address
											hlv.isBoogieBool);
//											hlv.isWrappedBool, hlv.isPointer, hlv.isOnHeap);
					

					if (underlyingType instanceof CPrimitive) {
						CPrimitive cp = (CPrimitive) this.lrVal.cType;
//						ResultExpression readResult;
						switch (cp.getType()) {
						case CHAR:
						case INT:
//							heapReadType = new InferredType(Type.Integer);
							rex = memoryHandler.getReadCall(
//									main, heapReadType, hlv.getAddress(), new CPointer(this.lrVal.cType));
									main, addressRVal);
							newStmt.addAll(rex.stmt);
							newDecl.addAll(rex.decl);
							newAuxVars.putAll(rex.auxVars);	
							newValue = (RValue) rex.lrVal;
							break;
						case FLOAT:
						case DOUBLE:
//							heapReadType = new InferredType(Type.Real);
							rex = memoryHandler.getReadCall(
//									main, heapReadType, hlv.getAddress(), new CPointer(this.lrVal.cType));
									main, addressRVal);
							newStmt.addAll(rex.stmt);
							newDecl.addAll(rex.decl);
							newAuxVars.putAll(rex.auxVars);	
							newValue = (RValue) rex.lrVal;	
							break;
						case VOID:
							//(in this case we return nothing, because this should not be read anyway..)
//							throw new UnsupportedSyntaxException("void should have been cast before dereferencing");
							break;
//						case BOOL:
						default:
							throw new UnsupportedSyntaxException(loc, "..");
						}
					} else if (underlyingType instanceof CPointer) {
//						heapReadType = new InferredType(Type.Pointer);
						rex = memoryHandler.getReadCall(
//								main, heapReadType, hlv.getAddress(), new CPointer(this.lrVal.cType));
									main, addressRVal);
						newStmt.addAll(rex.stmt);
						newDecl.addAll(rex.decl);
						newAuxVars.putAll(rex.auxVars);	
						newValue = (RValue) rex.lrVal;
					} else if (underlyingType instanceof CArray) {
//						CArray caType = (CArray) underlyingType;
//						assert caType.getDimensions().length > 0 : "the outermost subscript should have removed the arrayType";
////						heapReadType = new InferredType(caType.getValueType());
////						heapReadType = new InferredType(Type.Pointer);
//						rex = memoryHandler.getReadCall(
////								main, heapReadType, hlv.getAddress(), new CPointer(this.lrVal.cType));
//									main, addressRVal);
//						newStmt.addAll(rex.stmt);
//						newDecl.addAll(rex.decl);
//						newAuxVars.putAll(rex.auxVars);	
//						newValue = (RValue) rex.lrVal;
						return null; //"you can't assign arrays in C"
					} else if (underlyingType instanceof CEnum) {
					} else if (underlyingType instanceof CStruct) {
//						CStruct structType = (CStruct) underlyingType;
						rex = readStructFromHeap(main, structHandler, memoryHandler, loc, 
//								hlv.getAddress(), structType);
									addressRVal);
						newStmt.addAll(rex.stmt);
						newDecl.addAll(rex.decl);
						newAuxVars.putAll(rex.auxVars);	
						newValue = (RValue) rex.lrVal;	
					} else if (underlyingType instanceof CNamed) {
						assert false : "This should not be the case as we took the underlying type.";
					} else {
						throw new UnsupportedSyntaxException(loc, "..");
					}
//					newValue.isOnHeap = lrVal.isOnHeap;
//					newValue.isPointer = lrVal.isPointer;
					newValue.isBoogieBool = lrVal.isBoogieBool;
					rex = new ResultExpression(newStmt, newValue, newDecl,
					        newAuxVars, this.overappr, this.unionFieldIdToCType);
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
			StructHandler structHandler, MemoryHandler memoryHandler, ILocation loc,
			RValue address) {
//			Expression structOnHeapAddress, CStruct structType) {
		
		Expression structOnHeapAddress = address.getValue();
//		CStruct structType = (CStruct) ((CPointer) address.cType).pointsToType;
		CStruct structType = (CStruct) address.cType.getUnderlyingType();
		
		ResultExpression result = null;
		
		Expression startAddress = structOnHeapAddress;
		Expression currentStructBaseAddress = null;
		Expression currentStructOffset = null;
		if (startAddress instanceof StructConstructor) {
			currentStructBaseAddress = ((StructConstructor) startAddress).getFieldValues()[0];
			currentStructOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		} else {
			currentStructBaseAddress = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			currentStructOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		}
//		Expression currentStructBaseAddress = MemoryHandler.getPointerBaseAddress(structOnHeapAddress, loc);
//		Expression currentStructOffset = MemoryHandler.getPointerOffset(structOnHeapAddress, loc);

		//everything for the new Result
		ArrayList<Statement> newStmt = new ArrayList<Statement>();
		ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		LinkedHashMap<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

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
				CPrimitive cp = (CPrimitive) underlyingType;
				switch (cp.getType()) {
				case CHAR:
				case INT:
					typeOnHeap = new InferredType(Type.Integer);
					break;
//				case BOOL:
				default:
					throw new UnsupportedSyntaxException(loc, "..");
				}
				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
//						typeOnHeap,
//						structOnHeapAddress, //fieldTypes[i]);//TODO: or take the underlying type??
//						structType);
						address);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CPointer) {
				InferredType typeOnHeap = new InferredType(Type.Integer);
				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
//						typeOnHeap,
//						structOnHeapAddress, //fieldTypes[i]);//TODO: or take the underlying type??
//						structType);
						address);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CArray) {
				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CEnum) {
				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CStruct) {
				//sae = {base: currentStructBaseAddress, offset: currentStructOffset + thisFieldOffset }
				Expression innerStructOffset = 
						StructHandler.getStructOrUnionOffsetConstantExpression(loc, memoryHandler, fieldIds[i], structType);
//						StructHandler.getStructOffsetConstantExpression(loc, fieldIds[i], underlyingType);
				Expression innerStructAddress = MemoryHandler.constructPointerFromBaseAndOffset(currentStructBaseAddress, 
						new BinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, 
								currentStructOffset, 
								innerStructOffset),
								loc);
				
				RValue newAddress = new RValue(address);
				newAddress.value = innerStructAddress;
//				newAddress.cType= new CPointer(underlyingType);
				newAddress.cType= underlyingType;

				fieldRead = readStructFromHeap(main, structHandler, memoryHandler, 
//						loc, innerStructAddress, (CStruct) underlyingType);
						loc, newAddress);

				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CNamed) {
				assert false : "This should not be the case as we took the underlying type.";
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}	


			assert fieldRead.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
			fieldValues.add(((RValue) fieldRead.lrVal).getValue());

		}
		StructConstructor sc = new StructConstructor(loc, 
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));

		result = new ResultExpression(newStmt, new RValue(sc, structType),
		        newDecl, newAuxVars, this.overappr, this.unionFieldIdToCType);

		return result;
	}
	
	
	/**
	 * Add all declaration, statements, auxvars, etc. from another 
	 * ResultExpression. Lock the other ResultExpression afterwards to indicate
	 * that the other Result expression should not be used any more. 
	 */
	public void addAll(ResultExpression re) {
		this.decl.addAll(re.decl);
		this.stmt.addAll(re.stmt);
		this.auxVars.putAll(re.auxVars);
		this.overappr.addAll(overappr);
		re.lock();
	}
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
