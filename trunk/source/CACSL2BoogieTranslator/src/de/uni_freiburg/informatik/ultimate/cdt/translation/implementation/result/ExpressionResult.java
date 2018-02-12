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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PRDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 * @date 01.02.2012
 */
public class ExpressionResult extends Result {
	/**
	 * Statement list.
	 */
	public final List<Statement> mStmt;
	/**
	 * the LRValue may contain the contents of a memory cell or its address or both
	 */
	public LRValue mLrVal;
	/**
	 * Declaration list. Some translations need to declare some temporary variables, which we do here.
	 */
	public final List<Declaration> mDecl; // FIXME: could we also use the more special type VariableDeclaration here??

	/**
	 * A list of overapproximation flags.
	 */
	public final List<Overapprox> mOverappr;

	/**
	 * Auxiliary variables occurring in this result. The variable declaration of the var is mapped to the exact location
	 * for that it was constructed.
	 */
	public final Map<VariableDeclaration, ILocation> mAuxVars;

	/**
	 * We store off-heap unions as Boogie structs.
	 * When we write a field of an off-heap union, we must havoc all the other "neighbour" fields of the union.
	 * If this ExpressionResult represents a field in an off-heap union then this member contains information about the
	 * union fields that must be havocced if this union field is written.
	 */
	public final List<ExpressionResult> mOtherUnionFields;

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
	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars, final List<Overapprox> overapproxList,
			final List<ExpressionResult> uField2CType) {
		super(null);
		mStmt = stmt;
		mLrVal = lrVal;
		mDecl = decl;
		mAuxVars = auxVars;
		mOverappr = overapproxList;
		mOtherUnionFields = uField2CType;
	}

	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars, final List<Overapprox> overapproxList) {
		this(stmt, lrVal, decl, auxVars, overapproxList, Collections.emptyList());
	}

	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars) {
		this(stmt, lrVal, decl, auxVars, new ArrayList<Overapprox>(), Collections.emptyList());
	}

	public ExpressionResult(final LRValue lrVal, final Map<VariableDeclaration, ILocation> auxVars,
			final List<Overapprox> overapproxList) {
		this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(), auxVars, overapproxList,
				Collections.emptyList());
	}

	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal) {
		this(stmt, lrVal, new ArrayList<Declaration>(), new LinkedHashMap<VariableDeclaration, ILocation>(),
				new ArrayList<Overapprox>(), Collections.emptyList());
	}

	public ExpressionResult(final LRValue lrVal, final Map<VariableDeclaration, ILocation> auxVars) {
		this(new ArrayList<Statement>(), lrVal, new ArrayList<Declaration>(), auxVars);
	}

	public ExpressionResult(final LRValue lrVal) {
		this(lrVal, new LinkedHashMap<VariableDeclaration, ILocation>());
	}

	/**
	 * Construct a new {@link ExpressionResult} without an {@link LRValue} whose statements, declarations, auxVars and
	 * overapproximations contain all respective elements of resExprs. TODO: This could remove the old copy constructor
	 * one it is not used any more.
	 */
	public static ExpressionResult copyStmtDeclAuxvarOverapprox(final ExpressionResult... resExprs) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		for (final ExpressionResult resExpr : resExprs) {
			builder.addStatements(resExpr.mStmt);
			builder.addDeclarations(resExpr.mDecl);
			builder.putAuxVars(resExpr.mAuxVars);
			builder.addOverapprox(resExpr.mOverappr);
			if (resExpr.mOtherUnionFields != null && !resExpr.mOtherUnionFields.isEmpty()) {
				builder.addNeighbourUnionFields(resExpr.mOtherUnionFields);
			}
		}
		builder.setLrVal(null); // just for being explicit
		return builder.build();
	}

	public ExpressionResult switchToRValueIfNecessary(final Dispatcher main, final ILocation loc) {

		final MemoryHandler memoryHandler = main.mCHandler.getMemoryHandler();
		final StructHandler structHandler = main.mCHandler.getStructHandler();

		final ExpressionResult result;
		if (mLrVal == null) {
			result = this;
		} else if (mLrVal instanceof RValue) {
			replaceCFunctionByCPointer();
			replaceEnumByInt();
			result = this;
		} else if (mLrVal instanceof LocalLValue) {
			if (main instanceof PRDispatcher) {
				// we are in prerun mode
				if (mLrVal.getCType().getUnderlyingType() instanceof CArray) {
					// move it on-heap
					((PRDispatcher) main).moveArrayAndStructIdsOnHeap(loc, mLrVal.getValue(), mAuxVars);
				}
			} else {
				if (mLrVal.getCType().getUnderlyingType() instanceof CArray) {
					throw new AssertionError("on-heap/off-heap bug: array " + mLrVal.toString() + " has to be on-heap");
				}
			}
			final CType underlyingType = mLrVal.getCType().getUnderlyingType();
			final CType resultType;
			if (underlyingType instanceof CArray) {
				resultType = new CPointer(((CArray) underlyingType).getValueType());
			} else if (underlyingType instanceof CFunction) {
				resultType = new CPointer(underlyingType);
			} else if (underlyingType instanceof CEnum) {
				resultType = new CPrimitive(CPrimitives.INT);
			} else {
				resultType = underlyingType;
			}
			final RValue newRVal = new RValue(((LocalLValue) mLrVal).getValue(), resultType, mLrVal.isBoogieBool());
			result = new ExpressionResult(mStmt, newRVal, mDecl, mAuxVars, mOverappr, mOtherUnionFields);
		} else if (mLrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) mLrVal;
			CType underlyingType = mLrVal.getCType().getUnderlyingType();
			if (underlyingType instanceof CEnum) {
				underlyingType = new CPrimitive(CPrimitives.INT);
			}

			final RValue newValue;
			if (underlyingType instanceof CPrimitive) {
				final ExpressionResult rex = memoryHandler.getReadCall(hlv.getAddress(), underlyingType);
				result = copyStmtDeclAuxvarOverapprox(this, rex);
				newValue = (RValue) rex.mLrVal;
			} else if (underlyingType instanceof CPointer) {
				final ExpressionResult rex = memoryHandler.getReadCall(hlv.getAddress(), underlyingType);
				result = copyStmtDeclAuxvarOverapprox(this, rex);
				newValue = (RValue) rex.mLrVal;
			} else if (underlyingType instanceof CArray) {
				final CArray cArray = (CArray) underlyingType;
				// ExpressionResult rex = readArrayFromHeap(main, structHandler,
				// memoryHandler, loc, hlv.getAddress(), cArray);
				// result = copyStmtDeclAuxvarOverapprox(this, rex);
				result = copyStmtDeclAuxvarOverapprox(this);
				newValue = new RValue(hlv.getAddress(), new CPointer(cArray.getValueType()), false, false);
			} else if (underlyingType instanceof CEnum) {
				throw new AssertionError("handled above");
			} else if (underlyingType instanceof CStruct) {
				final ExpressionResult rex = readStructFromHeap(main, structHandler, memoryHandler, loc,
						hlv.getAddress(), (CStruct) underlyingType);
				result = copyStmtDeclAuxvarOverapprox(this, rex);
				newValue = (RValue) rex.mLrVal;
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else if (underlyingType instanceof CFunction) {
				result = copyStmtDeclAuxvarOverapprox(this);
				newValue = new RValue(hlv.getAddress(), new CPointer(underlyingType), false, false);
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}
			result.mLrVal = newValue;
		} else {
			throw new AssertionError("an LRValue that is not null, and no LocalLValue, RValue or HeapLValue???");
		}
		return result;
	}

	/**
	 * Read the contents of a struct (given as a pointer) from the heap recursively (for nested structs) returning a
	 * StructConstructor.
	 *
	 * @param main
	 * @param structHandler
	 * @param memoryHandler
	 * @param loc
	 * @param structOnHeapAddress
	 * @param structType
	 * @return A result whose value is a StructConstructor and whose statements make the necessary calls to fill the
	 *         items inside the StructConstructor correctly
	 */
	ExpressionResult readStructFromHeap(final Dispatcher main, final StructHandler structHandler,
			final MemoryHandler memoryHandler, final ILocation loc, final Expression structOnHeapAddress,
			final CStruct structType) {

		final Expression startAddress = structOnHeapAddress;
		Expression currentStructBaseAddress = null;
		Expression currentStructOffset = null;
		if (startAddress instanceof StructConstructor) {
			currentStructBaseAddress = ((StructConstructor) startAddress).getFieldValues()[0];
			currentStructOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		} else {
			currentStructBaseAddress = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			currentStructOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		}

		// everything for the new Result
		final ArrayList<Statement> newStmt = new ArrayList<>();
		final ArrayList<Declaration> newDecl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> newAuxVars = new LinkedHashMap<>();

		final String[] fieldIds = structType.getFieldIds();
		final CType[] fieldTypes = structType.getFieldTypes();

		// the new Arrays for the StructConstructor
		final ArrayList<String> fieldIdentifiers = new ArrayList<>();
		final ArrayList<Expression> fieldValues = new ArrayList<>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			CType underlyingType;
			if (fieldTypes[i] instanceof CNamed) {
				underlyingType = ((CNamed) fieldTypes[i]).getUnderlyingType();
			} else {
				underlyingType = fieldTypes[i];
			}

			// ResultExpression fieldRead = null;
			final LRValue fieldLRVal;
			if (underlyingType instanceof CPrimitive) {
				final ExpressionResult fieldRead = (ExpressionResult) structHandler.readFieldInTheStructAtAddress(main,
						loc, i, structOnHeapAddress, structType);
				fieldLRVal = fieldRead.mLrVal;
				newStmt.addAll(fieldRead.mStmt);
				newDecl.addAll(fieldRead.mDecl);
				newAuxVars.putAll(fieldRead.mAuxVars);
			} else if (underlyingType instanceof CPointer) {
				final ExpressionResult fieldRead = (ExpressionResult) structHandler.readFieldInTheStructAtAddress(main,
						loc, i, structOnHeapAddress, structType);
				fieldLRVal = fieldRead.mLrVal;
				newStmt.addAll(fieldRead.mStmt);
				newDecl.addAll(fieldRead.mDecl);
				newAuxVars.putAll(fieldRead.mAuxVars);
			} else if (underlyingType instanceof CArray) {

				final ExpressionResult xres1 = readArrayFromHeap(main, structHandler, memoryHandler, loc,
						structOnHeapAddress, (CArray) underlyingType);
				final ExpressionResult xres = xres1;

				fieldLRVal = xres.mLrVal;
				newStmt.addAll(xres.mStmt);
				newDecl.addAll(xres.mDecl);
				newAuxVars.putAll(xres.mAuxVars);

				// fieldRead = (ResultExpression) structHandler.readFieldInTheStructAtAddress(
				// main, memoryHandler, loc, fieldIds[i],
				// address);
				// newStmt.addAll(fieldRead.stmt);
				// newDecl.addAll(fieldRead.decl);
				// newAuxVars.putAll(fieldRead.auxVars);
				// throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CEnum) {
				// like CPrimitive..
				final ExpressionResult fieldRead = (ExpressionResult) structHandler.readFieldInTheStructAtAddress(main,
						loc, i, structOnHeapAddress, structType);
				fieldLRVal = fieldRead.mLrVal;
				newStmt.addAll(fieldRead.mStmt);
				newDecl.addAll(fieldRead.mDecl);
				newAuxVars.putAll(fieldRead.mAuxVars);
				// throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingType instanceof CStruct) {

				final Expression innerStructOffset =
						memoryHandler.getTypeSizeAndOffsetComputer().constructOffsetForField(loc, structType, i);

				final ExpressionTranslation exprTrans = ((CHandler) main.mCHandler).getExpressionTranslation();
				final Expression offsetSum = exprTrans.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
						currentStructOffset, exprTrans.getCTypeOfPointerComponents(), innerStructOffset,
						exprTrans.getCTypeOfPointerComponents());
				final Expression innerStructAddress =
						MemoryHandler.constructPointerFromBaseAndOffset(currentStructBaseAddress, offsetSum, loc);

				final ExpressionResult fieldRead = readStructFromHeap(main, structHandler, memoryHandler, loc,
						innerStructAddress, (CStruct) underlyingType);

				fieldLRVal = fieldRead.mLrVal;
				newStmt.addAll(fieldRead.mStmt);
				newDecl.addAll(fieldRead.mDecl);
				newAuxVars.putAll(fieldRead.mAuxVars);
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}

			// assert fieldRead.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
			// fieldValues.add(((RValue) fieldRead.lrVal).getValue());
			if (fieldLRVal instanceof RValue) {
				fieldValues.add(fieldLRVal.getValue());
			} else if (fieldLRVal instanceof HeapLValue) {
				fieldValues.add(((HeapLValue) fieldLRVal).getAddress());
			} else {
				throw new UnsupportedOperationException();
			}

		}
		final StructConstructor sc =
				new StructConstructor(loc, fieldIdentifiers.toArray(new String[fieldIdentifiers.size()]),
						fieldValues.toArray(new Expression[fieldValues.size()]));

		final ExpressionResult result = new ExpressionResult(newStmt, new RValue(sc, structType), newDecl, newAuxVars,
				mOverappr, mOtherUnionFields);
		return result;
	}

	public ExpressionResult readArrayFromHeap(final Dispatcher main, final StructHandler structHandler,
			final MemoryHandler memoryHandler, final ILocation loc, final Expression address, final CArray arrayType) {
		final HeapLValue resultValue;
//		List<Declaration> decl = new ArrayList<>();
//		List<Statement> stmt = new ArrayList<>();
//		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
//		final ArrayList<Overapprox> overApp = new ArrayList<>();
		ExpressionResultBuilder builder = new ExpressionResultBuilder();

		if (!(arrayType.getValueType().getUnderlyingType() instanceof CArray)) {
			final ExpressionTranslation exprTrans = ((CHandler) main.mCHandler).getExpressionTranslation();
			final BigInteger dimBigInteger = exprTrans.extractIntegerValue(arrayType.getBound());
			if (dimBigInteger == null) {
				throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
			}
			final int dim = dimBigInteger.intValue();

			final String newArrayId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.ARRAYCOPY, arrayType);
			final VarList newArrayVl = new VarList(loc, new String[] { newArrayId }, new ArrayType(loc, new String[0],
					new ASTType[] { main.mTypeHandler.cType2AstType(loc, arrayType.getBound().getCType()) },
					main.mTypeHandler.cType2AstType(loc, arrayType.getValueType())));
			final VariableDeclaration newArrayDec =
					new VariableDeclaration(loc, new Attribute[0], new VarList[] { newArrayVl });
			resultValue = new HeapLValue(new IdentifierExpression(loc, newArrayId), arrayType, null);
//			builder.setLrVal(new HeapLValue(new IdentifierExpression(loc, newArrayId), arrayType, null));

//			decl.add(newArrayDec);
//			auxVars.put(newArrayDec, loc);
			builder.addDeclaration(newArrayDec);
			builder.putAuxVar(newArrayDec, loc);

			final Expression arrayStartAddress = address;
			Expression newStartAddressBase = null;
			Expression newStartAddressOffset = null;
			if (arrayStartAddress instanceof StructConstructor) {
				newStartAddressBase = ((StructConstructor) arrayStartAddress).getFieldValues()[0];
				newStartAddressOffset = ((StructConstructor) arrayStartAddress).getFieldValues()[1];
			} else {
				newStartAddressBase = MemoryHandler.getPointerBaseAddress(arrayStartAddress, loc);
				newStartAddressOffset = MemoryHandler.getPointerOffset(arrayStartAddress, loc);
			}

			final Expression valueTypeSize = memoryHandler.calculateSizeOf(loc, arrayType.getValueType());

			Expression arrayEntryAddressOffset = newStartAddressOffset;

			for (int pos = 0; pos < dim; pos++) {

				ExpressionResult readRex;
				final Expression readAddress = MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase,
						arrayEntryAddressOffset, loc);
				if (arrayType.getValueType().getUnderlyingType() instanceof CStruct) {
					readRex = readStructFromHeap(main, structHandler, memoryHandler, loc, readAddress,
							(CStruct) arrayType.getValueType().getUnderlyingType());
				} else {
					readRex = memoryHandler.getReadCall(readAddress, arrayType.getValueType());
				}
				builder.addAllExceptLrValue(readRex);
				if (builder.getLrVal() == null) {
					builder.setLrVal(readRex.getLrValue());
				} else {
					builder.resetLrVal(readRex.getLrValue());
				}
//				decl.addAll(readRex.mDecl);
//				stmt.addAll(readRex.mStmt);
//				auxVars.putAll(readRex.mAuxVars);
//				overApp.addAll(readRex.mOverappr);

				final ArrayLHS aAcc = ExpressionFactory.constructNestedArrayLHS(loc, new VariableLHS(loc, newArrayId),
						new Expression[] { exprTrans.constructLiteralForIntegerType(loc,
								new CPrimitive(CPrimitives.INT), BigInteger.valueOf(pos)) });
//				final ExpressionResult assRex = ((CHandler) main.mCHandler).makeAssignment(main, loc, stmt,
//						new LocalLValue(aAcc, arrayType.getValueType(), null), (RValue) readRex.mLrVal, decl, auxVars,
//						mOverappr);
				final ExpressionResult assRex = ((CHandler) main.mCHandler).makeAssignment(main, loc,
						new LocalLValue(aAcc, arrayType.getValueType(), null), Collections.emptyList(), builder.build()
						);
				builder = new ExpressionResultBuilder()
						.addAllExceptLrValue(assRex)
						.setLrVal(assRex.getLrValue());
//				decl = assRex.mDecl;
//				stmt = assRex.mStmt;
//				auxVars = assRex.mAuxVars;
//				overApp.addAll(assRex.mOverappr);

				arrayEntryAddressOffset = exprTrans.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
						arrayEntryAddressOffset, exprTrans.getCTypeOfPointerComponents(), valueTypeSize,
						exprTrans.getCTypeOfPointerComponents());
			}
		} else {
			throw new UnsupportedSyntaxException(loc,
					"we need to generalize this to nested and/or variable length arrays");
		}
//		final ExpressionResult xres1 = new ExpressionResult(stmt, xfieldHeapLValue, decl, auxVars, overApp);
//		return xres1;
		builder.setOrResetLrVal(resultValue);
		return builder.build();
	}

	/**
	 * Add all declaration, statements, auxvars, etc. from another ResultExpression.
	 */
	public void addAll(final ExpressionResult re) {
		mDecl.addAll(re.mDecl);
		mStmt.addAll(re.mStmt);
		mAuxVars.putAll(re.mAuxVars);
		mOverappr.addAll(re.mOverappr);
	}

	public void addStatement(final Statement stmt) {
		mStmt.add(stmt);
	}

	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has CType enum, then replace it by CType int. If
	 * an enum variable occurs as an RValue we use this method to replace its type by int.
	 */
	private void replaceEnumByInt() {
		if (mLrVal instanceof RValue) {
			final RValue old = (RValue) mLrVal;
			if (old.getCType() instanceof CEnum) {
				final CPrimitive intType = new CPrimitive(CPrimitives.INT);
				mLrVal = new RValue(old.getValue(), intType, old.isBoogieBool(), old.isIntFromPointer());
			} else {
				// do nothing
			}
		} else {
			throw new UnsupportedOperationException("replaceEnumByInt only applicable for RValues");
		}
	}

	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has CType CFunction, then replace it by CType
	 * CPointer. If a function occurs as an RValue we use this method to replace its type by CPointer. 6.3.2.1 of C11
	 * says: A function designator is an expression that has function type. Except when it is the operand of the sizeof
	 * operator, the _Alignof operator,65) or the unary & operator, a function designator with type ‘‘function returning
	 * type’’ is converted to an expression that has type ‘‘pointer to function returning type’’.
	 */
	private void replaceCFunctionByCPointer() {
		if (mLrVal instanceof RValue) {
			final RValue old = (RValue) mLrVal;
			if (old.getCType() instanceof CFunction) {
				final CPointer pointerType = new CPointer(old.getCType());
				mLrVal = new RValue(old.getValue(), pointerType, old.isBoogieBool(), old.isIntFromPointer());
			} else {
				// do nothing
			}
		} else {
			throw new UnsupportedOperationException("replaceEnumByInt only applicable for RValues");
		}
	}

	/**
	 * Convert Expression of some type to an expression of boolean type. If the expression expr
	 * <ul>
	 * <li>has type boolean we return expr
	 * <li>has type int we return <i>expr != 0</i>
	 * <li>has type real we return <i>expr != 0.0</i>
	 * <li>has type $Pointer$ we return <i>expr != #NULL</i>
	 * </ul>
	 * Other types are not supported. If the expression was obtained by a conversion from bool to int, we try to get rid
	 * of the former conversion instead of applying a new one.
	 */
	private static RValue toBoolean(final ILocation loc, final RValue rVal,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler) {
		assert !rVal.isBoogieBool();
		CType underlyingType = rVal.getCType().getUnderlyingType();
		underlyingType = CEnum.replaceEnumWithInt(underlyingType);
		final Expression zero = expressionTranslation.constructZero(loc, underlyingType);
		final Expression resultEx;
		if (underlyingType instanceof CPrimitive) {
			resultEx = expressionTranslation.constructBinaryEqualityExpression(loc, IASTBinaryExpression.op_notequals,
					rVal.getValue(), rVal.getCType(), zero, underlyingType);
		} else if (underlyingType instanceof CPointer) {
			resultEx = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, rVal.getValue(),
					zero);
		} else {
			throw new UnsupportedSyntaxException(loc, "unsupported type " + underlyingType);
		}
		return new RValue(resultEx, new CPrimitive(CPrimitives.INT), true);
	}

	/**
	 * int <code>x</code> of form <code>y ? 1 : 0</code> becomes <code>!y ? 1 : 0</code> /** int <code>x</code> becomes
	 * <code>x == 0 ? 1 : 0</code>
	 */
	public void rexIntToBoolIfNecessary(final ILocation loc, final ExpressionTranslation expressionTranslation,
			final MemoryHandler memoryHandler) {
		if (!(mLrVal instanceof RValue)) {
			throw new UnsupportedOperationException("only RValue can switch");
		}
		if (mLrVal.isBoogieBool()) {
			// do nothing
		} else {
			mLrVal = toBoolean(loc, (RValue) mLrVal, expressionTranslation, memoryHandler);
		}
	}

	/** boolean <code>p</code> becomes <code>!p ? 1 : 0</code> */
	public void rexBoolToIntIfNecessary(final ILocation loc, final ExpressionTranslation expressionTranslation) {
		if (!(mLrVal instanceof RValue)) {
			throw new UnsupportedOperationException("only RValue can switch");
		}
		if (mLrVal.isBoogieBool()) {
			mLrVal = RValue.boolToInt(loc, (RValue) mLrVal, expressionTranslation);
		} else {
			// do nothing
		}
	}

	@Override
	public String toString() {
		return "ExpressionResult, LrVal: " + mLrVal.toString();
	}

	public LRValue getLrValue() {
		return mLrVal;
	}

	public List<Statement> getStatements() {
		return Collections.unmodifiableList(mStmt);
	}

	public List<Declaration> getDeclarations() {
		return Collections.unmodifiableList(mDecl);
	}

	public List<Overapprox> getOverapprs() {
		return Collections.unmodifiableList(mOverappr);
	}

	public Map<VariableDeclaration, ILocation> getAuxVars() {
		return Collections.unmodifiableMap(mAuxVars);
	}

	public Collection<ExpressionResult> getNeighbourUnionFields() {
		return Collections.unmodifiableCollection(mOtherUnionFields);
	}
}
