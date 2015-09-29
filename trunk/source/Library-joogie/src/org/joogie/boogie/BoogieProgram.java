/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.boogie;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;
import org.joogie.HeapMode;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.BinOpExpression.Operator;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.ArrArrayType;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.HeapType;
import org.joogie.boogie.types.RefArrayType;
import org.joogie.util.Util;

/**
 * @author schaef
 */
public class BoogieProgram {

	private LinkedList<BoogieAxiom> mBoogieAxioms;
	private Set<BoogieProcedure> mBoogieProcedures;
	private Set<Variable> mGlobalsVars;
	private Set<Variable> mTypeVariables;

	private Variable mNull;
	private Variable mNullIntArray;
	private Variable mNullRealArray;
	private Variable mNullRefArray;
	private Variable mSizeArrayInt;
	private Variable mSizeArrayReal;
	private Variable mSizeArrayRef;
	private Variable mSizeString;
	private Variable mSizeArrayIndex;
	private Variable mHeapVariable;
	private final Logger mLogger;

	public BoogieProgram(Logger logger) {
		mLogger = logger;
		mBoogieAxioms = new LinkedList<BoogieAxiom>();
		mBoogieProcedures = new HashSet<BoogieProcedure>();
		mGlobalsVars = new HashSet<Variable>();
		mTypeVariables = new HashSet<Variable>();

		mNull = new Variable("$null", BoogieBaseTypes.getRefType(), true);
		mNullIntArray = new Variable("$intArrNull", BoogieBaseTypes.getIntArrType(), true);
		mNullRealArray = new Variable("$realArrNull", BoogieBaseTypes.getRealArrType(), true);
		mNullRefArray = new Variable("$refArrNull", BoogieBaseTypes.getRefArrType(), true);
		mSizeArrayInt = new Variable("$intArrSize",
				new BoogieArrayType("$intarrsizetype", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType()),
				true);
		mSizeArrayReal = new Variable("$realArrSize",
				new BoogieArrayType("$realarrsizetype", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getIntType()),
				true);
		mSizeArrayRef = new Variable("$refArrSize",
				new BoogieArrayType("$refarrsizetype", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntType()),
				true);
		mSizeString = new Variable("$stringSize",
				new BoogieArrayType("$stringsizetype", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntType()),
				true);
		mSizeArrayIndex = new Variable("$arrSizeIdx", BoogieBaseTypes.getIntType(), true);
		mHeapVariable = new Variable("$HeapVar", new HeapType());

		// setup the BoogieAxioms

		// axiom ($arrSizeIdx==-1); : array size is stored outside the usable
		// bounds
		BoogieAxiom ba = new BoogieAxiom(
				new BinOpExpression(Operator.Eq, mSizeArrayIndex, new UboundedIntConstant(-1L)));
		mBoogieAxioms.add(ba);

	}

	public Set<BoogieProcedure> getProcedures() {
		return mBoogieProcedures;
	}

	public Set<Variable> getTypeVariables() {
		return mTypeVariables;
	}

	public void addProcedure(BoogieProcedure proc) {
		this.mBoogieProcedures.add(proc);
	}

	public Variable getHeapVariable() {
		return mHeapVariable;
	}

	public void addProcedures(Collection<BoogieProcedure> procs) {
		this.mBoogieProcedures.addAll(procs);
	}

	public void addGlobalVar(Variable v) {
		this.mGlobalsVars.add(v);
	}

	public void addTypeVariable(Variable v) {
		this.mTypeVariables.add(v);
	}

	public void addBoogieAxiom(BoogieAxiom axiom) {
		mBoogieAxioms.add(axiom);
	}

	public List<BoogieAxiom> getAxioms() {
		return mBoogieAxioms;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Variable getNullReference() {
		return mNull;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Expression getArraySizeExpression(Expression arrvar) {
		Expression ret = null;
		BoogieType t = arrvar.getType();
		if (t == BoogieBaseTypes.getIntArrType()) {
			ret = new ArrayReadExpression(this.mSizeArrayInt, new ArrayReadExpression(arrvar, mSizeArrayIndex));
		} else if (t == BoogieBaseTypes.getRealArrType()) {
			ret = new ArrayReadExpression(this.mSizeArrayReal, new ArrayReadExpression(arrvar, mSizeArrayIndex));
		} else if (t instanceof RefArrayType) {
			ret = new ArrayReadExpression(this.mSizeArrayRef, new ArrayReadExpression(arrvar, mSizeArrayIndex));
		} else if (t instanceof ArrArrayType) {
			mLogger.error("MultiArraySize is not implemented");
			Variable tmp = new Variable("$fresh" + (++Util.runningNumber).toString(), BoogieBaseTypes.getIntType());
			this.mGlobalsVars.add(tmp);
			ret = tmp;
		} else {
			mLogger.error(t.toBoogie());
			mLogger.error(
					"Size of of non-array: [" + arrvar.toBoogie() + "] type: [" + arrvar.getType().toBoogie() + "]");
		}
		return ret;
	}

	public Expression getStringLenExpression(Expression arrvar) {
		return new ArrayReadExpression(this.mSizeString, arrvar);
	}

	public Variable getStringSize() {
		return mSizeString;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Expression getArrayNullReference(BoogieType nestedArrayType) {
		if (nestedArrayType == BoogieBaseTypes.getIntType()) {
			return mNullIntArray;
		} else if (nestedArrayType == BoogieBaseTypes.getRealType()) {
			return mNullRealArray;
		} else if (nestedArrayType instanceof BoogieObjectType) {
			return mNullRefArray;
		} else if (nestedArrayType instanceof BoogieArrayType) {
			mLogger.error("Multi Arrays are not implementd");
			Variable tmp = new Variable("$fresh" + (++Util.runningNumber).toString(), nestedArrayType);
			this.mGlobalsVars.add(tmp);
			return tmp;
		}
		return null;
	}

	public String toLegacyBoogie(HeapMode heapmode) {
		StringBuilder sb = new StringBuilder();

		sb.append("type " + BoogieBaseTypes.getRefType().toBoogie() + ";\n");
		sb.append("type " + BoogieBaseTypes.getRealType().toBoogie() + ";\n");
		sb.append("type " + BoogieBaseTypes.getClassConstType().toBoogie() + ";\n");

		if (heapmode == HeapMode.Default) {
			sb.append("type Field x;\n");
			sb.append("var " + mHeapVariable.toBoogie() + " : " + mHeapVariable.getType().toBoogie() + ";\n");
		}
		sb.append("\n");

		sb.append("const unique " + mNull.toBoogie() + " : " + mNull.getType().toBoogie() + " ;\n");

		if (heapmode == HeapMode.Default) {
			sb.append("const unique " + mNullIntArray.toBoogie() + " : " + mNullIntArray.getType().toBoogie() + " ;\n");
			sb.append(
					"const unique " + mNullRealArray.toBoogie() + " : " + mNullRealArray.getType().toBoogie() + " ;\n");
			sb.append("const unique " + mNullRefArray.toBoogie() + " : " + mNullRefArray.getType().toBoogie() + " ;\n");
			sb.append("\n");
		}

		sb.append("const unique " + mSizeArrayIndex.toBoogie() + " : " + mSizeArrayIndex.getType().toBoogie() + ";\n");

		if (heapmode == HeapMode.Default) {
			sb.append("var " + mSizeArrayInt.toBoogie() + " : " + mSizeArrayInt.getType().toBoogie() + ";\n");
			sb.append("var " + mSizeArrayReal.toBoogie() + " : " + mSizeArrayReal.getType().toBoogie() + ";\n");
			sb.append("var " + mSizeArrayRef.toBoogie() + " : " + mSizeArrayRef.getType().toBoogie() + ";\n");
			sb.append("\n");
			sb.append("var " + mSizeString.toBoogie() + " : " + mSizeString.getType().toBoogie() + ";\n");
		}

		sb.append("\n");

		sb.append("//built-in axioms \n");
		for (BoogieAxiom axiom : mBoogieAxioms) {
			sb.append(axiom.toBoogie());
			sb.append(";\n");
		}

		sb.append("\n");
		sb.append("//note: new version doesn't put helpers in the perlude anymore");
		sb.append("//Prelude finished \n");

		for (Variable v : mTypeVariables) {
			sb.append("const unique " + v.toBoogie() + " : " + v.getType().toBoogie() + " ;\n");
		}
		sb.append("\n");

		sb.append("\n\n");

		for (Variable v : mGlobalsVars) {
			if (v.isConstUnique()) {
				sb.append("const unique ");
			} else {
				sb.append("var ");
			}

			sb.append(v.toBoogie());
			sb.append(" : ");
			sb.append(v.getType().toBoogie());
			sb.append(";\n");
		}

		sb.append("\n\n");

		for (BoogieProcedure p : mBoogieProcedures) {
			sb.append(p.toBoogie());
			sb.append("\n\n");
		}

		return sb.toString();
	}

	public Variable getIntArraySize() {
		return mSizeArrayInt;
	}

	public Variable getRealArraySize() {
		return mSizeArrayReal;
	}

	public Variable getRefArraySize() {
		return mSizeArrayRef;
	}

	public Variable getNullIntArray() {
		return mNullIntArray;
	}

	public Variable getNullRealArray() {
		return mNullRealArray;
	}

	public Variable getNullRefArray() {
		return mNullRefArray;
	}

	public Variable getSizeIndexArray() {
		return mSizeArrayIndex;
	}

	public Variable getSizeArrayInt() {
		return mSizeArrayInt;
	}

	public Variable getSizeArrayReal() {
		return mSizeArrayReal;
	}

	public Variable getSizeArrayRef() {
		return mSizeArrayRef;
	}

	public Variable getSizeString() {
		return mSizeString;
	}

	public Set<Variable> getGlobalVariables() {
		return mGlobalsVars;
	}

}
