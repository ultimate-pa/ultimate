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
import org.joogie.util.Log;
import org.joogie.util.Util;

/**
 * @author schaef
 */
public class BoogieProgram {

	private LinkedList<BoogieAxiom> boogieAxioms = new LinkedList<BoogieAxiom>();

	private HashSet<BoogieProcedure> boogieProcedures = new HashSet<BoogieProcedure>();
	private HashSet<Variable> globalsVars = new HashSet<Variable>();
	private HashSet<Variable> typeVariables = new HashSet<Variable>();

	public HashSet<BoogieProcedure> getProcedures() {
		return this.boogieProcedures;
	}

	public HashSet<Variable> getTypeVariables() {
		return this.typeVariables;
	}

	public void addProcedure(BoogieProcedure proc) {
		this.boogieProcedures.add(proc);
	}

	public void addProcedures(Collection<BoogieProcedure> procs) {
		this.boogieProcedures.addAll(procs);
	}

	public void addGlobalVar(Variable v) {
		this.globalsVars.add(v);
	}

	public void addTypeVariable(Variable v) {
		this.typeVariables.add(v);
	}

	private Variable nullVariable = new Variable("$null", BoogieBaseTypes.getRefType(), true);

	private Variable intArrNullVariable = new Variable("$intArrNull", BoogieBaseTypes.getIntArrType(), true);
	private Variable realArrNullVariable = new Variable("$realArrNull", BoogieBaseTypes.getRealArrType(), true);
	private Variable refArrNullVariable = new Variable("$refArrNull", BoogieBaseTypes.getRefArrType(), true);

	public Variable intArrSize = new Variable("$intArrSize",
			new BoogieArrayType("$intarrsizetype", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType()), true);

	public Variable realArrSize = new Variable("$realArrSize",
			new BoogieArrayType("$realarrsizetype", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getIntType()), true);

	public Variable refArrSize = new Variable("$refArrSize",
			new BoogieArrayType("$refarrsizetype", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntType()), true);

	public Variable stringSize = new Variable("$stringSize",
			new BoogieArrayType("$stringsizetype", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntType()), true);

	private Variable arrSizeIdx = new Variable("$arrSizeIdx", BoogieBaseTypes.getIntType(), true);

	/**
	 * in the javascript tranlator, the heapvariable is overwritten by the one
	 * given by the simplified javascript
	 */
	public Variable heapVariable = new Variable("$HeapVar", new HeapType());

	/**
	 * C-tor
	 */
	private BoogieProgram() {
		// setup the BoogieAxioms

		// axiom ($arrSizeIdx==-1); : array size is stored outside the usable
		// bounds
		BoogieAxiom ba = new BoogieAxiom(new BinOpExpression(Operator.Eq, arrSizeIdx, new UboundedIntConstant(-1L)));
		this.boogieAxioms.add(ba);

	}

	/**
	 * Singleton object
	 */
	private static BoogieProgram instance = null;

	/**
	 * Returns the Singleton object
	 * 
	 * @return Singleton object
	 */
	public static BoogieProgram v() {
		if (null == instance) {
			instance = new BoogieProgram();
		}
		return instance;
	}

	/**
	 * Resets the Singleton object
	 */
	public static void resetInstance() {
		instance = null;
	}

	public void addBoogieAxiom(BoogieAxiom axiom) {
		boogieAxioms.add(axiom);
	}

	public List<BoogieAxiom> getAxioms() {
		return boogieAxioms;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Variable getNullReference() {
		return nullVariable;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Expression getArraySizeExpression(Expression arrvar) {
		Expression ret = null;
		BoogieType t = arrvar.getType();
		if (t == BoogieBaseTypes.getIntArrType()) {
			ret = new ArrayReadExpression(this.intArrSize, new ArrayReadExpression(arrvar, arrSizeIdx));
		} else if (t == BoogieBaseTypes.getRealArrType()) {
			ret = new ArrayReadExpression(this.realArrSize, new ArrayReadExpression(arrvar, arrSizeIdx));
		} else if (t instanceof RefArrayType) {
			ret = new ArrayReadExpression(this.refArrSize, new ArrayReadExpression(arrvar, arrSizeIdx));
		} else if (t instanceof ArrArrayType) {
			Log.error("MultiArraySize is not implemented");
			Variable tmp = new Variable("$fresh" + (++Util.runningNumber).toString(), BoogieBaseTypes.getIntType());
			this.globalsVars.add(tmp);
			ret = tmp;
		} else {
			Log.error(t.toBoogie());
			Log.error("Size of of non-array: [" + arrvar.toBoogie() + "] type: [" + arrvar.getType().toBoogie() + "]");
		}
		return ret;
	}

	public Expression getStringLenExpression(Expression arrvar) {
		return new ArrayReadExpression(this.stringSize, arrvar);
	}

	// TODO: this has to be moved to the different translators!!!!
	public Expression getArrayNullReference(BoogieType nestedArrayType) {
		if (nestedArrayType == BoogieBaseTypes.getIntType()) {
			return intArrNullVariable;
		} else if (nestedArrayType == BoogieBaseTypes.getRealType()) {
			return realArrNullVariable;
		} else if (nestedArrayType instanceof BoogieObjectType) {
			return refArrNullVariable;
		} else if (nestedArrayType instanceof BoogieArrayType) {
			Log.error("Multi Arrays are not implementd");
			Variable tmp = new Variable("$fresh" + (++Util.runningNumber).toString(), nestedArrayType);
			this.globalsVars.add(tmp);
			return tmp;
		}
		return null;
	}

	public String toBoogie(HeapMode heapmode) {
		StringBuilder sb = new StringBuilder();

		sb.append("type " + BoogieBaseTypes.getRefType().toBoogie() + ";\n");
		sb.append("type " + BoogieBaseTypes.getRealType().toBoogie() + ";\n");
		sb.append("type " + BoogieBaseTypes.getClassConstType().toBoogie() + ";\n");

		if (heapmode == HeapMode.Default) {
			sb.append("type Field x;\n");
			sb.append("var " + heapVariable.toBoogie() + " : " + heapVariable.getType().toBoogie() + ";\n");
		}
		sb.append("\n");

		sb.append("const unique " + nullVariable.toBoogie() + " : " + nullVariable.getType().toBoogie() + " ;\n");

		if (heapmode == HeapMode.Default) {
			sb.append("const unique " + intArrNullVariable.toBoogie() + " : " + intArrNullVariable.getType().toBoogie()
					+ " ;\n");
			sb.append("const unique " + realArrNullVariable.toBoogie() + " : "
					+ realArrNullVariable.getType().toBoogie() + " ;\n");
			sb.append("const unique " + refArrNullVariable.toBoogie() + " : " + refArrNullVariable.getType().toBoogie()
					+ " ;\n");
			sb.append("\n");
		}

		sb.append("const unique " + arrSizeIdx.toBoogie() + " : " + arrSizeIdx.getType().toBoogie() + ";\n");

		if (heapmode == HeapMode.Default) {
			sb.append("var " + intArrSize.toBoogie() + " : " + intArrSize.getType().toBoogie() + ";\n");
			sb.append("var " + realArrSize.toBoogie() + " : " + realArrSize.getType().toBoogie() + ";\n");
			sb.append("var " + refArrSize.toBoogie() + " : " + refArrSize.getType().toBoogie() + ";\n");
			sb.append("\n");
			sb.append("var " + stringSize.toBoogie() + " : " + stringSize.getType().toBoogie() + ";\n");
		}

		sb.append("\n");

		sb.append("//built-in axioms \n");
		for (BoogieAxiom axiom : boogieAxioms) {
			sb.append(axiom.toBoogie());
			sb.append(";\n");
		}

		sb.append("\n");
		sb.append("//note: new version doesn't put helpers in the perlude anymore");
		sb.append("//Prelude finished \n");

		for (Variable v : typeVariables) {
			sb.append("const unique " + v.toBoogie() + " : " + v.getType().toBoogie() + " ;\n");
		}
		sb.append("\n");

		sb.append("\n\n");

		for (Variable v : globalsVars) {
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

		for (BoogieProcedure p : boogieProcedures) {
			sb.append(p.toBoogie());
			sb.append("\n\n");
		}

		return sb.toString();
	}

}
