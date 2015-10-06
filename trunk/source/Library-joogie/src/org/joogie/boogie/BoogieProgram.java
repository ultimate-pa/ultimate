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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.BinOpExpression.Operator;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.ArrArrayType;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogiePreludeTypes;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.HeapType;
import org.joogie.boogie.types.RefArrayType;
import org.joogie.util.Util;

/**
 * @author schaef
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class BoogieProgram {

	private static final String HEAP_VAR = "$HeapVar";
	private static final String ARRAY_SIZE_INDEX = "$arrSizeIdx";
	private static final String STRING_SIZE = "$stringSize";
	private static final String STRINGSIZETYPE = "$stringsizetype";

	private static final String REAL_ARR_SIZE = "$realArrSize";
	private static final String REALARRSIZETYPE = "$realarrsizetype";

	private static final String INT_ARR_SIZE = "$intArrSize";
	private static final String INTARRSIZETYPE = "$intarrsizetype";

	private static final String REF_ARR_SIZE = "$refArrSize";
	private static final String REFARRSIZETYPE = "$refarrsizetype";

	private static final String REF_ARR_NULL = "$refArrNull";
	private static final String REAL_ARR_NULL = "$realArrNull";
	private static final String INT_ARR_NULL = "$intArrNull";
	private static final String NULL = "$null";

	private final List<BoogieAxiom> mBoogieAxioms;
	private final Set<BoogieProcedure> mBoogieProcedures;
	private final Set<Variable> mGlobalsVars;
	private final Set<BoogieType> mTypes;

	private final Logger mLogger;
	private final Map<String, PreludeVariable> mPreludeVariables;

	public BoogieProgram(Logger logger) {
		mLogger = logger;
		mBoogieAxioms = new LinkedList<BoogieAxiom>();
		mBoogieProcedures = new HashSet<BoogieProcedure>();
		mGlobalsVars = new HashSet<Variable>();
		mTypes = new HashSet<BoogieType>();

		mPreludeVariables = new HashMap<String, PreludeVariable>();

		registerPreludeVariable(NULL, BoogiePreludeTypes.TYPE_REF, true);
		registerPreludeVariable(INT_ARR_NULL, BoogiePreludeTypes.TYPE_INT_ARRAY, true);
		registerPreludeVariable(REAL_ARR_NULL, BoogiePreludeTypes.TYPE_REAL_ARRAY, true);
		registerPreludeVariable(REF_ARR_NULL, BoogiePreludeTypes.TYPE_REF_ARRAY, true);
		registerPreludeVariable(INT_ARR_SIZE,
				new BoogieArrayType(INTARRSIZETYPE, BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT), false);
		registerPreludeVariable(REAL_ARR_SIZE,
				new BoogieArrayType(REALARRSIZETYPE, BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_INT),
				false);
		registerPreludeVariable(REF_ARR_SIZE,
				new BoogieArrayType(REFARRSIZETYPE, BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_INT), false);
		registerPreludeVariable(STRING_SIZE,
				new BoogieArrayType(STRINGSIZETYPE, BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_INT), false);
		registerPreludeVariable(ARRAY_SIZE_INDEX, BoogiePreludeTypes.TYPE_INT, true);
		registerPreludeVariable(HEAP_VAR, new HeapType(), false);

		// setup the BoogieAxioms

		// axiom ($arrSizeIdx==-1); : array size is stored outside the usable
		// bounds
		BoogieAxiom ba = new BoogieAxiom(
				new BinOpExpression(Operator.Eq, getArraySizeIndex(), new UboundedIntConstant(-1L)));
		mBoogieAxioms.add(ba);

	}

	private void registerPreludeVariable(final String name, final BoogieType type, boolean constUnique) {
		if (mPreludeVariables.put(name, new PreludeVariable(new Variable(name, type, constUnique))) != null) {
			throw new AssertionError("You cannot register multiple variables with the same name");
		}
	}

	private Variable getPreludeVar(String name) {
		PreludeVariable rtr = mPreludeVariables.get(name);
		if (rtr == null) {
			throw new AssertionError("You cannot use unregistered prelude variables: " + name);
		}
		useNestedTypeVars(rtr.Var);
		rtr.Used = true;
		return rtr.Var;
	}

	private void useNestedTypeVars(Variable var) {
		final BoogieType btype = var.getType();
		if (btype instanceof BoogieArrayType) {
//			getPreludeVar(((BoogieArrayType) btype).getName());
		}
	}

	public boolean isEmpty() {
		return mBoogieProcedures.isEmpty();
	}

	public Set<BoogieProcedure> getProcedures() {
		return mBoogieProcedures;
	}

	public Set<BoogieType> getTypeVariables() {
		return mTypes;
	}

	public void addProcedure(BoogieProcedure proc) {
		this.mBoogieProcedures.add(proc);
	}

	public Variable getHeapVariable() {
		return getPreludeVar(HEAP_VAR);
	}

	public void addProcedures(Collection<BoogieProcedure> procs) {
		this.mBoogieProcedures.addAll(procs);
	}

	public void addGlobalVar(Variable v) {
		this.mGlobalsVars.add(v);
	}

	public void addType(BoogieType v) {
		this.mTypes.add(v);
	}

	public void addBoogieAxiom(BoogieAxiom axiom) {
		mBoogieAxioms.add(axiom);
	}

	public List<BoogieAxiom> getAxioms() {
		return mBoogieAxioms;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Variable getNullReference() {
		return getPreludeVar(NULL);
	}

	public Variable getStringSize() {
		return getPreludeVar(STRING_SIZE);
	}

	public Expression getStringLenExpression(Expression arrvar) {
		return new ArrayReadExpression(getSizeString(), arrvar);
	}

	private Variable getArraySizeIndex() {
		return getPreludeVar(ARRAY_SIZE_INDEX);
	}

	// TODO: this has to be moved to the different translators!!!!
	public Expression getArraySizeExpression(Expression arrvar) {
		Expression ret = null;
		BoogieType t = arrvar.getType();
		if (t == BoogiePreludeTypes.TYPE_INT_ARRAY) {
			ret = new ArrayReadExpression(getIntArraySize(), new ArrayReadExpression(arrvar, getArraySizeIndex()));
		} else if (t == BoogiePreludeTypes.TYPE_REAL_ARRAY) {
			ret = new ArrayReadExpression(getRealArraySize(), new ArrayReadExpression(arrvar, getArraySizeIndex()));
		} else if (t instanceof RefArrayType) {
			ret = new ArrayReadExpression(getRefArraySize(), new ArrayReadExpression(arrvar, getArraySizeIndex()));
		} else if (t instanceof ArrArrayType) {
			mLogger.error("MultiArraySize is not implemented");
			Variable tmp = new Variable("$fresh" + (++Util.runningNumber).toString(), BoogiePreludeTypes.TYPE_INT);
			this.mGlobalsVars.add(tmp);
			ret = tmp;
		} else {
			mLogger.error(t.toBoogie());
			mLogger.error(
					"Size of of non-array: [" + arrvar.toBoogie() + "] type: [" + arrvar.getType().toBoogie() + "]");
		}
		return ret;
	}

	// TODO: this has to be moved to the different translators!!!!
	public Expression getArrayNullReference(BoogieType nestedArrayType) {
		if (nestedArrayType == BoogiePreludeTypes.TYPE_INT) {
			return getNullIntArray();
		} else if (nestedArrayType == BoogiePreludeTypes.TYPE_REAL) {
			return getNullRealArray();
		} else if (nestedArrayType instanceof BoogieObjectType) {
			return getNullRefArray();
		} else if (nestedArrayType instanceof BoogieArrayType) {
			mLogger.error("Multi Arrays are not implementd");
			Variable tmp = new Variable("$fresh" + (++Util.runningNumber).toString(), nestedArrayType);
			this.mGlobalsVars.add(tmp);
			return tmp;
		}
		return null;
	}

	public Set<Variable> getPreludeVariables() {
		return mPreludeVariables.entrySet().stream().filter(a -> a.getValue().Used).map(a -> a.getValue().Var)
				.collect(Collectors.toSet());
	}

	public Variable getIntArraySize() {
		return getPreludeVar(INT_ARR_SIZE);
	}

	public Variable getRealArraySize() {
		return getPreludeVar(REAL_ARR_SIZE);
	}

	public Variable getRefArraySize() {
		return getPreludeVar(REF_ARR_SIZE);
	}

	public Variable getNullIntArray() {
		return getPreludeVar(INT_ARR_NULL);
	}

	public Variable getNullRealArray() {
		return getPreludeVar(REAL_ARR_NULL);
	}

	public Variable getNullRefArray() {
		return getPreludeVar(REF_ARR_NULL);
	}

	public Variable getSizeIndexArray() {
		return getPreludeVar(ARRAY_SIZE_INDEX);
	}

	public Variable getSizeArrayReal() {
		return getPreludeVar(REAL_ARR_SIZE);
	}

	public Variable getSizeArrayRef() {
		return getPreludeVar(REF_ARR_SIZE);
	}

	public Variable getSizeString() {
		return getPreludeVar(STRING_SIZE);
	}

	public Set<Variable> getGlobalVariables() {
		return mGlobalsVars;
	}

	private static class PreludeVariable {
		private Variable Var;
		private boolean Used;

		private PreludeVariable(Variable var) {
			Var = var;
			Used = false;
		}
	}

}
