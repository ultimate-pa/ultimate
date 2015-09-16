/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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
/**
 * Describing a translation result for expressions.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PRDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class ExpressionResult extends Result {
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
	public final ArrayList<Declaration> decl; //FIXME: could we also use the more special type VariableDeclaration here??

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
    public ExpressionResult(ArrayList<Statement> stmt,
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
    
    
    public ExpressionResult(ArrayList<Statement> stmt,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overapproxList) {
    	this(stmt, lrVal, decl, auxVars, overapproxList, null);
    }

    
    public ExpressionResult(ArrayList<Statement> stmt,
            LRValue lrVal,
            ArrayList<Declaration> decl,
            Map<VariableDeclaration, ILocation> auxVars) {
        this(stmt, lrVal, decl,
                auxVars, new ArrayList<Overapprox>(), null);
    }

	public ExpressionResult(
			LRValue lrVal,
			Map<VariableDeclaration, ILocation> auxVars,
			List<Overapprox> overapproxList) {
	    this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(),
	            auxVars, overapproxList, null);
	}
	
	public ExpressionResult(ArrayList<Statement> stmt,
			LRValue lrVal) {
	    this(stmt, lrVal, new ArrayList<Declaration>(),
	            new LinkedHashMap<VariableDeclaration, ILocation>(), 
	            new ArrayList<Overapprox>(), null);
	}
	
	public ExpressionResult(
            LRValue lrVal,
            Map<VariableDeclaration, ILocation> auxVars) {
        this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(),
                auxVars);
    }

    public ExpressionResult(
            LRValue lrVal) {
        this(lrVal, new LinkedHashMap<VariableDeclaration, ILocation>());
    }
    
    /**
     * copy constructor
     * Note. Does _not_ construct a deep copy of the object.
     */
    public ExpressionResult(ExpressionResult rex) {
    	super(null);
    	this.stmt = rex.stmt;
    	this.lrVal = rex.lrVal;
    	this.decl = rex.decl;
    	this.auxVars = rex.auxVars;
    	this.overappr = rex.overappr;
    	this.unionFieldIdToCType = rex.unionFieldIdToCType;
    }
    

    /**
     * Construct a new {@link ExpressionResult} without an {@link LRValue}
     * whose statements, declarations, auxVars and overapproximations contain
     * all respective elements of resExprs.
     * TODO: This could remove the old copy constructor one it is not used
     * any more.
     */
    public static ExpressionResult copyStmtDeclAuxvarOverapprox(ExpressionResult... resExprs) {
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		Map<StructLHS, CType> unionFieldIdToCType = new LinkedHashMap<StructLHS, CType>();
		for (ExpressionResult resExpr : resExprs) {
			stmt.addAll(resExpr.stmt);
			decl.addAll(resExpr.decl);
			auxVars.putAll(resExpr.auxVars);
			overappr.addAll(resExpr.overappr);
			if (resExpr.unionFieldIdToCType != null) {
				unionFieldIdToCType.putAll(resExpr.unionFieldIdToCType);
			}
		}
		if (unionFieldIdToCType.isEmpty()) {
			unionFieldIdToCType = null;
		}
    	return new ExpressionResult(stmt, null, decl, auxVars, overappr, unionFieldIdToCType);
    }
    

	public ExpressionResult switchToRValueIfNecessary(Dispatcher main, MemoryHandler memoryHandler, 
			StructHandler structHandler, ILocation loc) {
		final ExpressionResult result;
		if (lrVal == null) {
			result =  this;
		} else if (lrVal instanceof RValue) {
			result =  this;
		} else if (lrVal instanceof LocalLValue) {
			if (!(main instanceof PRDispatcher) && (lrVal.getCType() instanceof CArray)) {
				throw new AssertionError("on-heap/off-heap bug: array " + lrVal.toString() + " has to be on-heap");
			}
			final CType underlyingType = this.lrVal.getCType().getUnderlyingType();
			final CType resultType;
			if (underlyingType instanceof CArray) {
				resultType = new CPointer(((CArray) underlyingType).getValueType());
			} else if (underlyingType instanceof CFunction) {
				resultType = new CPointer(underlyingType);
			} else {
				resultType = underlyingType;
			}
			RValue newRVal = new RValue(((LocalLValue) lrVal).getValue(),
					resultType, lrVal.isBoogieBool());
			result = new ExpressionResult(
					this.stmt, newRVal, this.decl, this.auxVars,
					        this.overappr, this.unionFieldIdToCType);
		} else if (lrVal instanceof HeapLValue) {
			HeapLValue hlv = (HeapLValue) lrVal;
			CType underlyingType = this.lrVal.getCType().getUnderlyingType();
			if (underlyingType instanceof CEnum) {
				underlyingType = new CPrimitive(PRIMITIVE.INT);
			}
		
			final RValue newValue;
			if (underlyingType instanceof CPrimitive) {
				ExpressionResult rex = memoryHandler.getReadCall(main, hlv.getAddress(), underlyingType);
				result = copyStmtDeclAuxvarOverapprox(this, rex);
				newValue = (RValue) rex.lrVal;
			} else if (underlyingType instanceof CPointer) {
				ExpressionResult rex = memoryHandler.getReadCall(main, hlv.getAddress(), underlyingType);
				result = copyStmtDeclAuxvarOverapprox(this, rex);				
				newValue = (RValue) rex.lrVal;
			} else if (underlyingType instanceof CArray) {
				CArray cArray = (CArray) underlyingType;
				ExpressionResult rex = readArrayFromHeap(main, structHandler,
						memoryHandler, loc, hlv.getAddress(), cArray);
				result = copyStmtDeclAuxvarOverapprox(this, rex);	
				newValue = new RValue(hlv.getAddress(), new CPointer(cArray.getValueType()), 
						false, false);
			} else if (underlyingType instanceof CEnum) {
				throw new AssertionError("handled above");
			} else if (underlyingType instanceof CStruct) {
				ExpressionResult rex = readStructFromHeap(main, structHandler, memoryHandler, loc, 
						hlv.getAddress(), (CStruct) underlyingType);
				result = copyStmtDeclAuxvarOverapprox(this, rex);				
				newValue = (RValue) rex.lrVal;
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else if (underlyingType instanceof CFunction) {
				result = copyStmtDeclAuxvarOverapprox(this);	
				newValue = new RValue(hlv.getAddress(), new CPointer(underlyingType), 
						false, false);
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}
			result.lrVal = newValue;
		} else {
			throw new AssertionError("an LRValue that is not null, and no LocalLValue, RValue or HeapLValue???");
		}
		return result;
	}

//	private ResultExpression readArrayFromHeap(Dispatcher main,
//			MemoryHandler memoryHandler, ILocation loc, RValue addressRVal) {
//		CArray arrayType = (CArray) addressRVal.cType.getUnderlyingType();
//		
//		Expression[] dims = arrayType.getDimensions();
//		
//		for (int i)
//				
//		return null;
//	}

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
	ExpressionResult readStructFromHeap(Dispatcher main, 
			StructHandler structHandler, MemoryHandler memoryHandler, ILocation loc,
			Expression structOnHeapAddress, CStruct structType) {
		
		ExpressionResult result = null;
		
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
		Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

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

//			ResultExpression fieldRead = null; 
			final LRValue fieldLRVal;
			if(underlyingType instanceof CPrimitive) {
				ExpressionResult fieldRead = (ExpressionResult) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
						structOnHeapAddress, structType);
				fieldLRVal = (RValue) fieldRead.lrVal;
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CPointer) {
				ExpressionResult fieldRead = (ExpressionResult) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
						structOnHeapAddress, structType);
				fieldLRVal = (RValue) fieldRead.lrVal;
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CArray) {
				
				ExpressionResult xres1 = readArrayFromHeap(main, structHandler,
						memoryHandler, loc, structOnHeapAddress, (CArray) underlyingType);
				ExpressionResult xres = xres1;
				
				fieldLRVal = (HeapLValue) xres.lrVal;
				newStmt.addAll(xres.stmt);
				newDecl.addAll(xres.decl);
				newAuxVars.putAll(xres.auxVars);
				
				
//				fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
//						main, memoryHandler, loc, fieldIds[i], 
//						address);
//				newStmt.addAll(fieldRead.stmt);
//				newDecl.addAll(fieldRead.decl);
//				newAuxVars.putAll(fieldRead.auxVars);
//				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CEnum) {
				//like CPrimitive..
				ExpressionResult fieldRead = (ExpressionResult) structHandler.readFieldInTheStructAtAddress(
						main, memoryHandler, loc, fieldIds[i], 
						structOnHeapAddress, structType);
				fieldLRVal = (RValue) fieldRead.lrVal;
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
//				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CStruct) {
				Expression innerStructOffset = 
						StructHandler.getStructOrUnionOffsetConstantExpression(loc, memoryHandler, fieldIds[i], structType);
				Expression innerStructAddress = MemoryHandler.constructPointerFromBaseAndOffset(currentStructBaseAddress, 
						new BinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, 
								currentStructOffset, 
								innerStructOffset),
								loc);
				
				ExpressionResult fieldRead = readStructFromHeap(main, structHandler, memoryHandler, 
						loc, innerStructAddress, (CStruct) underlyingType);

				fieldLRVal = (RValue) fieldRead.lrVal;
				newStmt.addAll(fieldRead.stmt);
				newDecl.addAll(fieldRead.decl);
				newAuxVars.putAll(fieldRead.auxVars);
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}	


//			assert fieldRead.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
//			fieldValues.add(((RValue) fieldRead.lrVal).getValue());
			if (fieldLRVal instanceof RValue) {
				fieldValues.add(fieldLRVal.getValue());
			} else if (fieldLRVal instanceof HeapLValue) {
				fieldValues.add(((HeapLValue) fieldLRVal).getAddress());
			} else {
				throw new UnsupportedOperationException();
			}
			

		}
		StructConstructor sc = new StructConstructor(loc, 
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));

		result = new ExpressionResult(newStmt, new RValue(sc, structType),
		        newDecl, newAuxVars, this.overappr, this.unionFieldIdToCType);

		return result;
	}

	public ExpressionResult readArrayFromHeap(Dispatcher main,
			StructHandler structHandler, MemoryHandler memoryHandler,
			ILocation loc, Expression address, CArray arrayType) {
		HeapLValue xfieldHeapLValue = null;
		ArrayList<Declaration> decl = new ArrayList<>();
		ArrayList<Statement> stmt = new ArrayList<>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		ArrayList<Overapprox> overApp = new ArrayList<>();

		if (arrayType.getDimensions().length == 1
				&& arrayType.getDimensions()[0] instanceof IntegerLiteral) {
			int dim = Integer.parseInt(((IntegerLiteral) arrayType.getDimensions()[0]).getValue());

			String newArrayId = main.nameHandler.getTempVarUID(SFO.AUXVAR.ARRAYCOPY);
			VarList newArrayVl = new VarList(loc, new String[] { newArrayId }, 
					new ArrayType(loc, new String[0], new ASTType[] { new PrimitiveType(loc, SFO.INT) }, 
							main.typeHandler.ctype2asttype(loc, arrayType.getValueType())));
			VariableDeclaration newArrayDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { newArrayVl });
			xfieldHeapLValue = new HeapLValue(new IdentifierExpression(loc, newArrayId), arrayType);
			
			decl.add(newArrayDec);
			auxVars.put(newArrayDec, loc);
			
			
			Expression arrayStartAddress = address;
			Expression newStartAddressBase = null;
			Expression newStartAddressOffset = null;
			if (arrayStartAddress instanceof StructConstructor) {
				newStartAddressBase = ((StructConstructor) arrayStartAddress).getFieldValues()[0];
				newStartAddressOffset = ((StructConstructor) arrayStartAddress).getFieldValues()[1];
			} else {
				newStartAddressBase = MemoryHandler.getPointerBaseAddress(arrayStartAddress, loc);
				newStartAddressOffset = MemoryHandler.getPointerOffset(arrayStartAddress, loc);
			}

			Expression valueTypeSize = memoryHandler.calculateSizeOf(arrayType.getValueType(), loc);

			Expression arrayEntryAddressOffset = newStartAddressOffset;

			for (int pos = 0; pos < dim; pos++) {
				
				ExpressionResult readRex;
				Expression readAddress = MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, arrayEntryAddressOffset, loc);
				if (arrayType.getValueType().getUnderlyingType() instanceof CStruct) {
					readRex = readStructFromHeap(main, structHandler, memoryHandler, loc,
							readAddress, (CStruct) arrayType.getValueType().getUnderlyingType());
				} else {
					readRex = memoryHandler.getReadCall(main, readAddress, 
							arrayType.getValueType());
				}
				decl.addAll(readRex.decl);
				stmt.addAll(readRex.stmt);
				auxVars.putAll(readRex.auxVars);
				overApp.addAll(readRex.overappr);

				ArrayLHS aAcc = new ArrayLHS(loc, new VariableLHS(loc, newArrayId),
						new Expression[] { new IntegerLiteral(loc, new Integer(pos).toString())} );
				ExpressionResult assRex = ((CHandler) main.cHandler).makeAssignment(main, loc, stmt, 
						new LocalLValue(aAcc, arrayType.getValueType()), (RValue) readRex.lrVal, decl, auxVars, overappr);
				decl = assRex.decl;
				stmt = assRex.stmt;
				auxVars = assRex.auxVars;
				overApp.addAll(assRex.overappr);

				arrayEntryAddressOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus, 
						arrayEntryAddressOffset, valueTypeSize, loc);
			}
		} else {
			throw new UnsupportedSyntaxException(loc, "we need to generalize this to nested and/or variable length arrays");
		}
		ExpressionResult xres1 = new ExpressionResult(stmt, xfieldHeapLValue, decl, auxVars, overApp);
		return xres1;
	}
	
	/**
	 * Add all declaration, statements, auxvars, etc. from another 
	 * ResultExpression. Lock the other ResultExpression afterwards to indicate
	 * that the other Result expression should not be used any more. 
	 */
	public void addAll(ExpressionResult re) {
		this.decl.addAll(re.decl);
		this.stmt.addAll(re.stmt);
		this.auxVars.putAll(re.auxVars);
		this.overappr.addAll(overappr);
	}
	
	
	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has
	 * CType enum, then replace it by CType int. If an enum variable occurs as
	 * an RValue we use this method to replace its type by int. 
	 */
	public void replaceEnumByInt() {
		if (this.lrVal instanceof RValue) {
			RValue old = (RValue) this.lrVal;
			if (old.getCType() instanceof CEnum) {
				CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
				this.lrVal = new RValue(old.getValue(), intType, old.isBoogieBool(), old.isIntFromPointer());
			} else {
				// do nothing
			}
		} else {
			throw new UnsupportedOperationException("replaceEnumByInt only applicable for RValues");
		}
	}
	
	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has CType
	 * CFunction, then replace it by CType CPointer. If a function occurs as an
	 * RValue we use this method to replace its type by CPointer. 6.3.2.1 of C11
	 * says: A function designator is an expression that has function type.
	 * Except when it is the operand of the sizeof operator, the _Alignof
	 * operator,65) or the unary & operator, a function designator with type
	 * ‘‘function returning type’’ is converted to an expression that has type 
	 * ‘‘pointer to function returning type’’.
	 */
	public void replaceCFunctionByCPointer() {
		if (this.lrVal instanceof RValue) {
			RValue old = (RValue) this.lrVal;
			if (old.getCType() instanceof CFunction) {
				CPointer pointerType = new CPointer(old.getCType());
				this.lrVal = new RValue(old.getValue(), pointerType, old.isBoogieBool(), old.isIntFromPointer());
			} else {
				// do nothing
			}
		} else {
			throw new UnsupportedOperationException("replaceEnumByInt only applicable for RValues");
		}
	}
}
