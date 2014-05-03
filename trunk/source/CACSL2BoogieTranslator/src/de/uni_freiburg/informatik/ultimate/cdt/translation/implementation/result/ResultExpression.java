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
    public ResultExpression(ArrayList<Statement> stmt,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overapproxList,
            Map<StructLHS, CType> uField2CType) {
        super(null);
        this.stmt = stmt;
        this.lrVal = lrVal;
        this.decl = decl;
        this.auxVars = auxVars;
        this.overappr = overapproxList;
        this.unionFieldIdToCType = uField2CType;
    }
    
    
    public ResultExpression(ArrayList<Statement> stmt,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overapproxList) {
    	this(stmt, lrVal, decl, auxVars, overapproxList, null);
    }
    
    public ResultExpression(ArrayList<Statement> stmt,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars) {
        this(stmt, lrVal, decl,
                auxVars, new ArrayList<Overapprox>(), null);
    }

	public ResultExpression(
			LRValue lrVal,
			Map<VariableDeclaration, ILocation> auxVars,
			List<Overapprox> overapproxList) {
	    this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(),
	            auxVars, overapproxList, null);
	}
	
	public ResultExpression(
            LRValue lrVal,
            Map<VariableDeclaration, ILocation> auxVars) {
        this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(),
                auxVars);
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
		if (lrVal == null) {
			return this;
		} else if (lrVal instanceof RValue) {
			return this;
		} else if (lrVal instanceof LocalLValue) {
			RValue newRVal = new RValue(((LocalLValue) lrVal).getValue(),
					        lrVal.cType, lrVal.isBoogieBool);
			return new ResultExpression(
					this.stmt, newRVal, this.decl, this.auxVars,
					        this.overappr, this.unionFieldIdToCType);
		} else if (lrVal instanceof HeapLValue) {
			if (m_Locked) {
				throw new AssertionError("this ResultExpression is already locked");
			}
			ResultExpression rex = null;
			HeapLValue hlv = (HeapLValue) lrVal;
			
			//retain already created stmt, decl, auxVars
			ArrayList<Statement> newStmt = new ArrayList<Statement>(this.stmt);
			ArrayList<Declaration> newDecl = new ArrayList<Declaration>(this.decl);
			LinkedHashMap<VariableDeclaration, ILocation> newAuxVars = 
					new LinkedHashMap<VariableDeclaration, ILocation>(this.auxVars); 
			RValue newValue = null;


			CType underlyingType = this.lrVal.cType instanceof CNamed ? 
					((CNamed) this.lrVal.cType).getUnderlyingType() :
						this.lrVal.cType;

					//has the type of what lies at that address
					RValue addressRVal = new RValue(hlv.getAddress(), this.lrVal.cType, 
											hlv.isBoogieBool);
					

					if (underlyingType instanceof CPrimitive) {
						CPrimitive cp = (CPrimitive) this.lrVal.cType;
						switch (cp.getType()) {
						case CHAR:
						case INT:
							rex = memoryHandler.getReadCall(
									main, addressRVal);
							newStmt.addAll(rex.stmt);
							newDecl.addAll(rex.decl);
							newAuxVars.putAll(rex.auxVars);	
							newValue = (RValue) rex.lrVal;
							break;
						case FLOAT:
						case DOUBLE:
							rex = memoryHandler.getReadCall(
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
						rex = memoryHandler.getReadCall(
									main, addressRVal);
						newStmt.addAll(rex.stmt);
						newDecl.addAll(rex.decl);
						newAuxVars.putAll(rex.auxVars);	
						newValue = (RValue) rex.lrVal;
					} else if (underlyingType instanceof CArray) {
//						return null; //"you can't assign arrays in C"
						throw new AssertionError("you can't assign arrays in C");
					} else if (underlyingType instanceof CEnum) {
					} else if (underlyingType instanceof CStruct) {
						rex = readStructFromHeap(main, structHandler, memoryHandler, loc, 
									addressRVal);
						newStmt.addAll(rex.stmt);
						newDecl.addAll(rex.decl);
						newAuxVars.putAll(rex.auxVars);	
						newValue = (RValue) rex.lrVal;	
					} else if (underlyingType instanceof CNamed) {
						throw new AssertionError("This should not be the case as we took the underlying type.");
					} else {
						throw new UnsupportedSyntaxException(loc, "..");
					}
					newValue.isBoogieBool = lrVal.isBoogieBool;
					rex = new ResultExpression(newStmt, newValue, newDecl,
					        newAuxVars, this.overappr, this.unionFieldIdToCType);
					return rex;
		} else {
			throw new AssertionError("an LRValue that is not null, and no LocalLValue, RValue or HeapLValue???");
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
		
		Expression structOnHeapAddress = address.getValue();
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
				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
						address);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CPointer) {
				InferredType typeOnHeap = new InferredType(Type.Integer);
				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
						address);
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CArray) {
				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CEnum) {
				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CStruct) {
				Expression innerStructOffset = 
						StructHandler.getStructOrUnionOffsetConstantExpression(loc, memoryHandler, fieldIds[i], structType);
				Expression innerStructAddress = MemoryHandler.constructPointerFromBaseAndOffset(currentStructBaseAddress, 
						new BinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, 
								currentStructOffset, 
								innerStructOffset),
								loc);
				
				RValue newAddress = new RValue(address);
				newAddress.value = innerStructAddress;
				newAddress.cType= underlyingType;

				fieldRead = readStructFromHeap(main, structHandler, memoryHandler, 
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