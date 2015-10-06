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

package org.joogie.soot.helper;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.BinOpExpression.Operator;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.UnaryExpression;
import org.joogie.boogie.expressions.UnaryExpression.UnaryOperator;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.types.ArrArrayType;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogiePreludeTypes;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.RefArrayType;

/**
 * @author schaef
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class OperatorFunctionFactory {

	private final BoogieProgramConstructionDecorator mProgDec;

	private Set<BoogieProcedure> mOperatorProcs;
	private Set<BoogieProcedure> mUsedOperatorProcs;

	private BoogieProcedure addInt, subInt, mulInt, divInt, modInt, cmpInt, eqInt, ltInt, leInt, gtInt, geInt, neInt,
			andInt, orInt, xorInt, shlInt, shrInt, ushrInt, negInt;

	private BoogieProcedure addReal, subReal, mulReal, divReal, modReal, cmpReal, eqReal, ltReal, leReal, gtReal,
			geReal, neReal, andReal, orReal, xorReal, shlReal, shrReal, ushrReal, negReal;

	private BoogieProcedure addRef, subRef, mulRef, divRef, modRef, cmpRef, eqRef, ltRef, leRef, gtRef, geRef, neRef,
			andRef, orRef, xorRef, shlRef, shrRef, ushrRef, negRef;

	private BoogieProcedure refToIntArr, refToRealArr, refToRefArr, intToReal, refToInt, realToInt, refArrToRef,
			realArrToRef, intArrToRef;

	private BoogieProcedure instanceofOp, newVariable;

	private BoogieProcedure eqRefArray, eqRealArray, eqIntArray;

	private LinkedList<BoogieProcedure> intOperators, refOperators, realOperators;

	private final Logger mLogger;

	OperatorFunctionFactory(final BoogieProgramConstructionDecorator progDec, final Logger logger) {
		mLogger = logger;
		mProgDec = progDec;
		mOperatorProcs = new HashSet<BoogieProcedure>();
		mUsedOperatorProcs = new HashSet<BoogieProcedure>();

		// TODO: What is this about? Did I write this?
		// /// BEGIN HACK
		// Need to create a dummy procedure for initialization
		BoogieProcedure dummy = new BoogieProcedure("dummy", null, false, false);
		// Save the unlucky procedure
		BoogieProcedure temp = mProgDec.getCurrentProcedure();

		mProgDec.setCurrentProcedure(dummy);
		init(mProgDec.getProgram());
		// Restore the procedure
		mProgDec.setCurrentProcedure(temp);
		// / END HACK
		// TODO: Do it right: when initializing parameters, the variable
		// factory should receive a reference to the current procedure
	}

	private void init(BoogieProgram prog) {
		newVariable = createProcedure("$newvariable", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_INT);
		mOperatorProcs.add(newVariable);

		instanceofOp = createProcedure("$instanceof", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_CLASS_CONST);
		mOperatorProcs.add(instanceofOp);

		eqIntArray = createProcedure("$eqintarray", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_INT_ARRAY,
				BoogiePreludeTypes.TYPE_INT_ARRAY);
		mOperatorProcs.add(eqIntArray);

		eqRealArray = createProcedure("$eqrealarray", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REAL_ARRAY,
				BoogiePreludeTypes.TYPE_REAL_ARRAY);
		mOperatorProcs.add(eqRealArray);

		eqRefArray = createProcedure("$eqrefarray", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REF_ARRAY,
				BoogiePreludeTypes.TYPE_REF_ARRAY);
		mOperatorProcs.add(eqRefArray);

		intArrToRef = createProcedure("$intarrtoref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_INT_ARRAY);
		mOperatorProcs.add(intArrToRef);

		realArrToRef = createProcedure("$realarrtoref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REAL_ARRAY);
		mOperatorProcs.add(realArrToRef);

		refArrToRef = createProcedure("$refarrtoref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REF_ARRAY);
		mOperatorProcs.add(refArrToRef);

		refToIntArr = createProcedure("$reftointarr", BoogiePreludeTypes.TYPE_INT_ARRAY, BoogiePreludeTypes.TYPE_REF);
		mOperatorProcs.add(refToIntArr);

		refToRealArr = createProcedure("$reftorealarr", BoogiePreludeTypes.TYPE_REAL_ARRAY, BoogiePreludeTypes.TYPE_REF);
		mOperatorProcs.add(refToRealArr);

		refToRefArr = createProcedure("$reftorefarr", BoogiePreludeTypes.TYPE_REF_ARRAY, BoogiePreludeTypes.TYPE_REF);
		mOperatorProcs.add(refToRefArr);

		intToReal = createProcedure("$inttoreal", BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_INT);
		mOperatorProcs.add(intToReal);

		refToInt = createProcedure("$reftoint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF);
		mOperatorProcs.add(refToInt);

		realToInt = createProcedure("$realtoint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL);
		mOperatorProcs.add(realToInt);

		negInt = new BoogieProcedure("$negInt", BoogiePreludeTypes.TYPE_INT, createNegIntExpression(),
				mProgDec.getUniqueUid());
		mOperatorProcs.add(negInt);

		negReal = createProcedure("$negReal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL);
		mOperatorProcs.add(negReal);

		negRef = createProcedure("$negRef", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF);
		mOperatorProcs.add(negRef);

		// Integer operations
		addInt = new BoogieProcedure("$addint", BoogiePreludeTypes.TYPE_INT,
				createBinOpExpression(Operator.Plus, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		subInt = new BoogieProcedure("$subint", BoogiePreludeTypes.TYPE_INT,
				createBinOpExpression(Operator.Minus, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		// TODO Don't create a procedure body for mul as Princess cannot deal
		// with that
		// mulInt = new BoogieProcedure("$mulint",
		// BoogieBaseTypes.getIntType(),
		// createBinOpExpression(Operator.Mul,
		// BoogieBaseTypes.getIntType()));
		mulInt = createProcedure("$mulint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);

		// TODO Don't create a procedure body for div as Princess cannot deal
		// with that
		// divInt = new BoogieProcedure("$divint",
		// BoogieBaseTypes.getIntType(), createBinOpExpression(Operator.Div,
		// BoogieBaseTypes.getIntType()) );
		divInt = createProcedure("$divint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);
		modInt = createProcedure("$modint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);

		eqInt = new BoogieProcedure("$eqint", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Eq, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		neInt = new BoogieProcedure("$neint", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Neq, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		ltInt = new BoogieProcedure("$ltint", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Lt, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		leInt = new BoogieProcedure("$leint", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Le, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		gtInt = new BoogieProcedure("$gtint", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Gt, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());
		geInt = new BoogieProcedure("$geint", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Ge, BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());

		cmpInt = new BoogieProcedure("$cmpint", BoogiePreludeTypes.TYPE_INT,
				createCmpExpression(BoogiePreludeTypes.TYPE_INT), mProgDec.getUniqueUid());

		andInt = createProcedure("$andint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);
		orInt = createProcedure("$orint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);
		xorInt = createProcedure("$xorint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);
		ushrInt = createProcedure("$ushrint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);
		shlInt = createProcedure("$shlint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);
		shrInt = createProcedure("$shrint", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_INT,
				BoogiePreludeTypes.TYPE_INT);

		intOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addInt, subInt, mulInt, divInt, modInt, cmpInt, eqInt, ltInt,
						leInt, gtInt, geInt, neInt, andInt, orInt, xorInt, shlInt, shrInt, ushrInt }));

		mOperatorProcs.addAll(intOperators);

		// Real operations
		// -------------------------------------------------------
		eqReal = new BoogieProcedure("$eqreal", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Eq, BoogiePreludeTypes.TYPE_REAL), mProgDec.getUniqueUid());
		neReal = new BoogieProcedure("$nereal", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Neq, BoogiePreludeTypes.TYPE_REAL), mProgDec.getUniqueUid());
		addReal = createProcedure("$addreal", BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		subReal = createProcedure("$subreal", BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		mulReal = createProcedure("$mulreal", BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		divReal = createProcedure("$divreal", BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		modReal = createProcedure("$modreal", BoogiePreludeTypes.TYPE_REAL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		ltReal = createProcedure("$ltreal", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		leReal = createProcedure("$lereal", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		gtReal = createProcedure("$gtreal", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		geReal = createProcedure("$gereal", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		andReal = createProcedure("$andreal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		orReal = createProcedure("$orreal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		xorReal = createProcedure("$xorreal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		ushrReal = createProcedure("$ushrreal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		shlReal = createProcedure("$shlreal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);
		shrReal = createProcedure("$shrreal", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REAL,
				BoogiePreludeTypes.TYPE_REAL);

		realOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addReal, subReal, mulReal, divReal, modReal, eqReal, ltReal,
						leReal, gtReal, geReal, neReal, andReal, orReal, xorReal, shlReal, shrReal, ushrReal }));

		mOperatorProcs.addAll(realOperators);

		// Ref operations
		addRef = createProcedure("$addref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		subRef = createProcedure("$subref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		mulRef = createProcedure("$mulref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		divRef = createProcedure("$divref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		modRef = createProcedure("$modref", BoogiePreludeTypes.TYPE_REF, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);

		eqRef = new BoogieProcedure("$eqref", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Eq, BoogiePreludeTypes.TYPE_REF), mProgDec.getUniqueUid());
		neRef = new BoogieProcedure("$neref", BoogiePreludeTypes.TYPE_BOOL,
				createLogOpExpression(Operator.Neq, BoogiePreludeTypes.TYPE_REF), mProgDec.getUniqueUid());

		ltRef = createProcedure("$ltref", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		leRef = createProcedure("$leref", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		gtRef = createProcedure("$gtref", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		geRef = createProcedure("$geref", BoogiePreludeTypes.TYPE_BOOL, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);

		andRef = createProcedure("$andref", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		orRef = createProcedure("$orref", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		xorRef = createProcedure("$xorref", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		ushrRef = createProcedure("$ushrref", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		shlRef = createProcedure("$shlref", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);
		shrRef = createProcedure("$shrref", BoogiePreludeTypes.TYPE_INT, BoogiePreludeTypes.TYPE_REF,
				BoogiePreludeTypes.TYPE_REF);

		refOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addRef, subRef, mulRef, divRef, modRef, eqRef, ltRef, leRef,
						gtRef, geRef, neRef, andRef, orRef, xorRef, shlRef, shrRef, ushrRef }));

		mOperatorProcs.addAll(refOperators);

		// The cmp operators for real and ref are created in the end,
		// because they use other prelude functions
		cmpReal = new BoogieProcedure("$cmpreal", BoogiePreludeTypes.TYPE_INT,
				createCmpExpression(BoogiePreludeTypes.TYPE_REAL), mProgDec.getUniqueUid());
		realOperators.add(cmpReal);
		mOperatorProcs.add(cmpReal);

		cmpRef = new BoogieProcedure("$cmpref", BoogiePreludeTypes.TYPE_INT,
				createCmpExpression(BoogiePreludeTypes.TYPE_REF), mProgDec.getUniqueUid());
		refOperators.add(cmpRef);

		mOperatorProcs.add(cmpRef); // operatorProcs now contains all prelude
									// functions

		// BoogieProgram.v().addProcedures(operatorProcs);
	}

	public SimpleHeapAccess createSimpleHeapAccess(Expression base, Expression field) {
		// TODO add assertions to guard memory access
		return new SimpleHeapAccess(mProgDec.getProgram().getHeapVariable(), base, field);
	}

	/**
	 * returns an uninterpreted function that can be used to create fresh
	 * heapvars
	 */
	public BoogieProcedure getNewVarProcedure() {
		mUsedOperatorProcs.add(newVariable);
		return newVariable;
	}

	public Expression createBinOp(String op, Expression left, Expression right) {
		Expression exp = null;
		op = op.trim();

		if (op.compareTo("+") == 0) {
			exp = getOperatorFun("add", left, right);
		} else if (op.compareTo("-") == 0) {
			exp = getOperatorFun("sub", left, right);
		} else if (op.compareTo("*") == 0) {
			exp = getOperatorFun("mul", left, right);
		} else if (op.compareTo("/") == 0) {
			exp = getOperatorFun("div", left, right);
		} else if (op.compareTo("%") == 0) {
			exp = getOperatorFun("mod", left, right);
		} else if (op.compareTo("cmp") == 0) {
			exp = getOperatorFun("cmp", left, right);
		} else if (op.compareTo("cmpl") == 0) {
			exp = getOperatorFun("cmp", left, right);
		} else if (op.compareTo("cmpg") == 0) {
			exp = getOperatorFun("cmp", left, right);
		} else if (op.compareTo("==") == 0) {
			exp = getOperatorFun("eq", left, right);
		} else if (op.compareTo("<") == 0) {
			exp = getOperatorFun("lt", left, right);
		} else if (op.compareTo(">") == 0) {
			exp = getOperatorFun("gt", left, right);
		} else if (op.compareTo("<=") == 0) {
			exp = getOperatorFun("le", left, right);
		} else if (op.compareTo(">=") == 0) {
			exp = getOperatorFun("ge", left, right);
		} else if (op.compareTo("!=") == 0) {
			exp = getOperatorFun("ne", left, right);
		} else if (op.compareTo("&") == 0) {
			exp = getOperatorFun("and", left, right);
		} else if (op.compareTo("|") == 0) {
			exp = getOperatorFun("or", left, right);
		} else if (op.compareTo("<<") == 0) { // Shiftl
			exp = getOperatorFun("shl", left, right);
		} else if (op.compareTo(">>") == 0) { // Shiftr
			exp = getOperatorFun("shr", left, right);
		} else if (op.compareTo(">>>") == 0) { // UShiftr
			exp = getOperatorFun("ushr", left, right);
		} else if (op.compareTo("^") == 0) { // XOR
			exp = getOperatorFun("xor", left, right);
		} else if (op.compareTo("instanceof") == 0) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(left);
			args.add(right);
			mUsedOperatorProcs.add(instanceofOp);
			exp = createInvokeExpression(instanceofOp, args);
		} else {
			throw new UnsupportedOperationException("Operator not handled: " + op);
		}
		return exp;
	}

	public Expression createNegOp(Expression exp) {
		BoogieProcedure proc = null;
		if (exp.getType() == BoogiePreludeTypes.TYPE_INT) {
			proc = negInt;
		} else if (exp.getType() == BoogiePreludeTypes.TYPE_REAL) {
			proc = negReal;
		} else if (exp.getType() instanceof BoogieObjectType) {
			proc = negRef;
		} else if (exp.getType() == BoogiePreludeTypes.TYPE_BOOL) {
			// Inline the negation operator for boolean expressions
			return new UnaryExpression(UnaryOperator.Not, exp);
		}
		if (proc != null) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			InvokeExpression e = createInvokeExpression(proc, args);
			mUsedOperatorProcs.add(proc);
			return e;
		}
		return null;
	}

	public Expression castIfNecessary(Expression exp, BoogieType targetType) {
		if (compareTypes(exp.getType(), targetType)) {
			return exp;
		} else {
			if (targetType == BoogiePreludeTypes.TYPE_INT) {
				return castToInt(exp);
			} else if (targetType == BoogiePreludeTypes.TYPE_REAL) {
				return castToReal(exp);
			} else if (targetType instanceof BoogieObjectType && exp.getType() instanceof BoogieArrayType) {
				return castArrayToRef(mProgDec.getProgram(), exp);
			} else if (targetType instanceof BoogieArrayType) {
				// special case if exp is a null constant:
				if (exp == mProgDec.getProgram().getNullReference()) {
					if (targetType instanceof ArrArrayType) {
						mLogger.debug("castIfNecessary: MultiArray not implemented - sound abstraction");
						return mProgDec.getFreshGlobalConstant(targetType);
					} else {
						return mProgDec.getProgram()
								.getArrayNullReference(((BoogieArrayType) targetType).getNestedType());
					}
				} else {
					return castToArray(mProgDec.getProgram(), exp, targetType);
				}
			} else {
				throw new AssertionError("Cannot cast " + exp.toBoogie() + " to " + targetType.toBoogie());
			}
		}
	}

	public Expression isNotNull(Expression e) {
		return createBinOp("!=", e, mProgDec.getProgram().getNullReference());
	}

	public Expression isNull(Expression e) {
		return createBinOp("==", e, mProgDec.getProgram().getNullReference());
	}

	public Expression getFreshHeapField(soot.Type t) {
		Expression exp = createNewHeapVariable();
		return castIfNecessary(exp, mProgDec.getTypeFactory().lookupBoogieType(t));
	}

	public Expression createNewHeapVariable() {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(mProgDec.getConstantFactory().createConst(mProgDec.getCache().getUniqueNumber()));
		return createInvokeExpression(getNewVarProcedure(), args);
	}

	public InvokeExpression createInvokeExpression(BoogieProcedure proc, LinkedList<Expression> args) {
		// The arguments might have to be casted to fit the parameter types.
		// Note that the first argument is the THIS pointer which has to be
		// ignored
		LinkedList<Expression> arguments = new LinkedList<Expression>();
		int offset = 0;
		if (!proc.isStatic()) {
			offset = 1;
			arguments.add(args.getFirst());
		}

		for (int i = 0; i < args.size() - offset; i++) {
			Expression exp = args.get(i + offset);
			BoogieType t = proc.lookupParameter(i).getType();
			arguments.add(castIfNecessary(exp, t));
		}
		return new InvokeExpression(proc, arguments);
	}

	public AssignStatement createAssignment(Expression lhs, Expression rhs) {
		Expression rhsExpression = castIfNecessary(rhs, lhs.getType());
		if (rhsExpression == null) {
			mLogger.error(rhs.toBoogie() + " cannot be casted");
			mLogger.error("from: " + rhs.getType().toBoogie() + " to: " + lhs.getType().toBoogie());
		}
		return new AssignStatement(lhs, rhsExpression);
	}

	public boolean isPreludeProcedure(BoogieProcedure proc) {
		// TODO: there might be certainly more beautiful ways to implement this
		// but the sake of having a class, this should be fine
		if (proc == negInt)
			return true;
		if (proc == negReal)
			return true;
		if (proc == negRef)
			return true;
		if (proc == eqIntArray)
			return true;
		if (proc == eqRealArray)
			return true;
		if (proc == eqRefArray)
			return true;
		if (proc == refToInt)
			return true;
		if (proc == realToInt)
			return true;
		if (proc == intToReal)
			return true;

		if (proc == refArrToRef)
			return true;
		if (proc == realArrToRef)
			return true;
		if (proc == intArrToRef)
			return true;

		if (proc == refToIntArr)
			return true;
		if (proc == refToRealArr)
			return true;
		if (proc == refToRefArr)
			return true;

		if (proc == instanceofOp)
			return true;
		if (proc == newVariable)
			return true;

		if (intOperators.contains(proc))
			return true;
		if (realOperators.contains(proc))
			return true;
		if (refOperators.contains(proc))
			return true;

		return false;
	}

	public Set<BoogieProcedure> getUsedPreludeProcedures() {
		return mUsedOperatorProcs;
	}

	private Expression getOperatorFun(String opcode, Expression l, Expression r) {
		LinkedList<BoogieProcedure> proctype = null;
		if (l.getType() == r.getType() && l.getType() == BoogiePreludeTypes.TYPE_INT) {
			proctype = intOperators;
		} else if (l.getType() == r.getType() && l.getType() == BoogiePreludeTypes.TYPE_REAL) {
			proctype = realOperators;
		} else if (l.getType() instanceof BoogieObjectType && r.getType() instanceof BoogieObjectType) {
			proctype = refOperators;
		} else if (l.getType() == BoogiePreludeTypes.TYPE_INT && r.getType() instanceof BoogieObjectType) {
			r = castToInt(r);
			proctype = intOperators;
		} else if (l.getType() instanceof BoogieObjectType && r.getType() == BoogiePreludeTypes.TYPE_INT) {
			l = castToInt(l);
			proctype = intOperators;
		} else if (l.getType() instanceof BoogieArrayType && r.getType() instanceof BoogieArrayType) {
			// TODO test,if there are more cases to consider
			if (opcode.compareTo("eq") == 0) {
				return compareArrayEquality(l, r);
			} else if (opcode.compareTo("ne") == 0) {
				return createNegOp(compareArrayEquality(l, r));
			}
		} else if (l == mProgDec.getProgram().getNullReference() && r.getType() instanceof BoogieArrayType) {
			l = mProgDec.getProgram().getArrayNullReference(((BoogieArrayType) r.getType()).getNestedType());
			if (opcode.compareTo("eq") == 0) {
				return compareArrayEquality(l, r);
			} else if (opcode.compareTo("ne") == 0) {
				return createNegOp(compareArrayEquality(l, r));
			}
		} else if (l.getType() instanceof BoogieArrayType && r == mProgDec.getProgram().getNullReference()) {
			r = mProgDec.getProgram().getArrayNullReference(((BoogieArrayType) l.getType()).getNestedType());
			if (opcode.compareTo("eq") == 0) {
				return compareArrayEquality(l, r);
			} else if (opcode.compareTo("ne") == 0) {
				return createNegOp(compareArrayEquality(l, r));
			}
		} else {
			throw new UnsupportedOperationException(
					"Types don't match: " + l.getType().getName() + " and " + r.getType().getName());
		}
		BoogieProcedure proc = findProcedureWithPrefix(opcode, proctype);

		if (proc != null) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(l);
			args.add(r);
			InvokeExpression e = createInvokeExpression(proc, args);
			mUsedOperatorProcs.add(proc);
			return e;
		}
		return null;
	}

	private Expression compareArrayEquality(Expression l, Expression r) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(l);
		args.add(r);
		if (l.getType() == BoogiePreludeTypes.TYPE_INT_ARRAY) {
			mUsedOperatorProcs.add(eqIntArray);
			return createInvokeExpression(eqIntArray, args);
		} else if (l.getType() == BoogiePreludeTypes.TYPE_REAL_ARRAY) {
			mUsedOperatorProcs.add(eqRealArray);
			return createInvokeExpression(eqRealArray, args);
		} else if (l.getType() instanceof RefArrayType) {
			mUsedOperatorProcs.add(eqRefArray);
			return createInvokeExpression(eqRefArray, args);
		} else if (l.getType() instanceof ArrArrayType) {
			throw new UnsupportedOperationException("compareArrayEquality: CASE not implemented");
		}
		throw new UnsupportedOperationException("compareArrayEquality: Type not implemented");
	}

	private BoogieProcedure findProcedureWithPrefix(String prefix, List<BoogieProcedure> l) {
		for (BoogieProcedure proc : l) {
			if (proc == null)
				continue; // This can only occur during the construction of the
							// singleton
			if (proc.getName().startsWith("$" + prefix))
				return proc;
		}

		mLogger.error("TODO!!! " + prefix); // TODO remove if there are no bugs
		// caused by this method
		return null;
	}

	private boolean compareTypes(BoogieType a, BoogieType b) {
		if (b instanceof BoogieObjectType && a instanceof RefArrayType) {
			mLogger.debug("comparing array with object type. this could be a bug");
		}

		if (a == b) {
			return true;
		} else if ((a instanceof BoogieObjectType && b instanceof BoogieObjectType)
				|| (a instanceof RefArrayType && b instanceof RefArrayType)) {
			return true;
		} else if (a instanceof ArrArrayType && b instanceof ArrArrayType) {
			return compareTypes(((ArrArrayType) a).getNestedType(), ((ArrArrayType) b).getNestedType());
		}
		return false;
	}

	private Expression castToInt(Expression exp) {
		if (exp.getType() == BoogiePreludeTypes.TYPE_INT) {
			return exp;
		} else if (exp.getType() == BoogiePreludeTypes.TYPE_REAL) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			mUsedOperatorProcs.add(realToInt);
			return createInvokeExpression(realToInt, args);
		} else if (exp.getType() instanceof BoogieObjectType) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			mUsedOperatorProcs.add(refToInt);
			return createInvokeExpression(refToInt, args);
		} else {
			return exp;
		}
	}

	private Expression castToReal(Expression exp) {
		if (exp.getType() == BoogiePreludeTypes.TYPE_INT) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			mUsedOperatorProcs.add(intToReal);
			return createInvokeExpression(intToReal, args);
		} else {
			return exp;
		}
	}

	private Expression castToArray(BoogieProgram prog, Expression exp, BoogieType arrtype) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		if (exp.getType() instanceof BoogieObjectType) {
			if (arrtype == BoogiePreludeTypes.TYPE_INT_ARRAY) {
				mUsedOperatorProcs.add(refToIntArr);
				return createInvokeExpression(refToIntArr, args);
			} else if (arrtype == BoogiePreludeTypes.TYPE_REAL_ARRAY) {
				mUsedOperatorProcs.add(refToRealArr);
				return createInvokeExpression(refToRealArr, args);
			} else if (arrtype instanceof RefArrayType) {
				return createInvokeExpression(getRefToRefArr(), args);
			} else if (arrtype instanceof ArrArrayType) {
				throw new UnsupportedOperationException("castToArray: multiarrays are not really implemented");
			}
		}
		throw new UnsupportedOperationException("castToArray: case is not implemented");
	}

	private Expression castArrayToRef(BoogieProgram prog, Expression exp) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		BoogieType arrtype = exp.getType();
		if (arrtype == BoogiePreludeTypes.TYPE_INT_ARRAY) {
			mUsedOperatorProcs.add(intArrToRef);
			return createInvokeExpression(intArrToRef, args);
		} else if (arrtype == BoogiePreludeTypes.TYPE_REAL_ARRAY) {
			mUsedOperatorProcs.add(realArrToRef);
			return createInvokeExpression(realArrToRef, args);
		} else if (arrtype instanceof RefArrayType) {
			mUsedOperatorProcs.add(refArrToRef);
			return createInvokeExpression(refArrToRef, args);
		} else {
			throw new UnsupportedOperationException("castToArray: case is not implemented");
		}
	}

	private Expression createBinOpExpression(BinOpExpression.Operator op, BoogieType t) {
		Variable x = mProgDec.createBoogieVariable("x", t);
		Variable y = mProgDec.createBoogieVariable("y", t);
		return new BinOpExpression(op, x, y);
	}

	private Expression createLogOpExpression(BinOpExpression.Operator op, BoogieType t) {
		Variable x = mProgDec.createBoogieVariable("x", t);
		Variable y = mProgDec.createBoogieVariable("y", t);
		return new BinOpExpression(op, x, y);
	}

	/*
	 * Creates a cmp operation (see
	 * http://www.netmite.com/android/mydroid/dalvik/docs/dalvik-bytecode.html)
	 * Perform the indicated floating point or long comparison, storing 0 if the
	 * two arguments are equal, 1 if the second argument is larger, or -1 if the
	 * first argument is larger.
	 */
	private Expression createCmpExpression(final BoogieType t) {
		final Variable x = mProgDec.createBoogieVariable("x", t);
		final Variable y = mProgDec.createBoogieVariable("y", t);

		if (t != BoogiePreludeTypes.TYPE_INT) {
			final Expression equality = createBinOp("==", x, y);
			final Expression comparison = createBinOp("<", x, y);
			return new IteExpression(comparison, new UboundedIntConstant(1L),
					new IteExpression(equality, new UboundedIntConstant(0L), new UboundedIntConstant(-1L)));
		} else {
			final Expression lt = new BinOpExpression(Operator.Lt, x, y);
			final Expression eq = new BinOpExpression(Operator.Eq, x, y);
			return new IteExpression(lt, new UboundedIntConstant(1L),
					new IteExpression(eq, new UboundedIntConstant(0L), new UboundedIntConstant(-1L)));
		}
	}

	private Expression createNegIntExpression() {
		Variable x = mProgDec.createBoogieVariable("x", BoogiePreludeTypes.TYPE_INT);
		return new IteExpression(new BinOpExpression(Operator.Eq, x, new UboundedIntConstant(0L)),
				new UboundedIntConstant(1L), new UboundedIntConstant(0L));

	}

	private BoogieProcedure createProcedure(String name, BoogieType rettype, BoogieType t) {
		return new BoogieProcedure(name, rettype, (new LinkedList<BoogieType>(Arrays.asList(new BoogieType[] { t }))),
				true);
	}

	private BoogieProcedure createProcedure(String name, BoogieType rettype, BoogieType t1, BoogieType t2) {
		return new BoogieProcedure(name, rettype,
				(new LinkedList<BoogieType>(Arrays.asList(new BoogieType[] { t1, t2 }))), true);
	}

	private BoogieProcedure getRefToRefArr() {
		mUsedOperatorProcs.add(refToRefArr);
		return refToRefArr;
	}
}
