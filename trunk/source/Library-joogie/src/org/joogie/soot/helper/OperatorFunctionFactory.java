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

import org.apache.log4j.Logger;
import org.joogie.HeapMode;
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
import org.joogie.boogie.types.BoogieBaseTypes;
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

	// TODO: Remove singleton pattern from this
	private HeapMode mHeapmode;
	private HashSet<BoogieProcedure> mOperatorProcs;

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
		newVariable = createProcedure("$newvariable", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntType());
		mOperatorProcs.add(newVariable);

		instanceofOp = createProcedure("$instanceof", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getClassConstType());
		mOperatorProcs.add(instanceofOp);

		eqIntArray = createProcedure("$eqintarray", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getIntArrType(),
				BoogieBaseTypes.getIntArrType());
		mOperatorProcs.add(eqIntArray);

		eqRealArray = createProcedure("$eqrealarray", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRealArrType(),
				BoogieBaseTypes.getRealArrType());
		mOperatorProcs.add(eqRealArray);

		eqRefArray = createProcedure("$eqrefarray", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRefArrType(),
				BoogieBaseTypes.getRefArrType());
		mOperatorProcs.add(eqRefArray);

		intArrToRef = createProcedure("$intarrtoref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getIntArrType());
		mOperatorProcs.add(intArrToRef);

		realArrToRef = createProcedure("$realarrtoref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRealArrType());
		mOperatorProcs.add(realArrToRef);

		refArrToRef = createProcedure("$refarrtoref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefArrType());
		mOperatorProcs.add(refArrToRef);

		refToIntArr = createProcedure("$reftointarr", BoogieBaseTypes.getIntArrType(), BoogieBaseTypes.getRefType());
		mOperatorProcs.add(refToIntArr);

		refToRealArr = createProcedure("$reftorealarr", BoogieBaseTypes.getRealArrType(), BoogieBaseTypes.getRefType());
		mOperatorProcs.add(refToRealArr);

		refToRefArr = createProcedure("$reftorefarr", BoogieBaseTypes.getRefArrType(), BoogieBaseTypes.getRefType());
		mOperatorProcs.add(refToRefArr);

		intToReal = createProcedure("$inttoreal", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getIntType());
		mOperatorProcs.add(intToReal);

		refToInt = createProcedure("$reftoint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType());
		mOperatorProcs.add(refToInt);

		realToInt = createProcedure("$realtoint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType());
		mOperatorProcs.add(realToInt);

		negInt = new BoogieProcedure("$negInt", BoogieBaseTypes.getIntType(), createNegIntExpression(),
				mProgDec.getUniqueUid());
		mOperatorProcs.add(negInt);

		negReal = createProcedure("$negReal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType());
		mOperatorProcs.add(negReal);

		negRef = createProcedure("$negRef", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType());
		mOperatorProcs.add(negRef);

		// Integer operations
		addInt = new BoogieProcedure("$addint", BoogieBaseTypes.getIntType(),
				createBinOpExpression(Operator.Plus, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		subInt = new BoogieProcedure("$subint", BoogieBaseTypes.getIntType(),
				createBinOpExpression(Operator.Minus, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		// TODO Don't create a procedure body for mul as Princess cannot deal
		// with that
		// mulInt = new BoogieProcedure("$mulint",
		// BoogieBaseTypes.getIntType(),
		// createBinOpExpression(Operator.Mul,
		// BoogieBaseTypes.getIntType()));
		mulInt = createProcedure("$mulint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());

		// TODO Don't create a procedure body for div as Princess cannot deal
		// with that
		// divInt = new BoogieProcedure("$divint",
		// BoogieBaseTypes.getIntType(), createBinOpExpression(Operator.Div,
		// BoogieBaseTypes.getIntType()) );
		divInt = createProcedure("$divint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());
		modInt = createProcedure("$modint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());

		eqInt = new BoogieProcedure("$eqint", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Eq, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		neInt = new BoogieProcedure("$neint", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Neq, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		ltInt = new BoogieProcedure("$ltint", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Lt, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		leInt = new BoogieProcedure("$leint", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Le, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		gtInt = new BoogieProcedure("$gtint", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Gt, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());
		geInt = new BoogieProcedure("$geint", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Ge, BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());

		cmpInt = new BoogieProcedure("$cmpint", BoogieBaseTypes.getIntType(),
				createCmpExpression(BoogieBaseTypes.getIntType()), mProgDec.getUniqueUid());

		andInt = createProcedure("$andint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());
		orInt = createProcedure("$orint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());
		xorInt = createProcedure("$xorint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());
		ushrInt = createProcedure("$ushrint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());
		shlInt = createProcedure("$shlint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());
		shrInt = createProcedure("$shrint", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getIntType(),
				BoogieBaseTypes.getIntType());

		intOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addInt, subInt, mulInt, divInt, modInt, cmpInt, eqInt, ltInt,
						leInt, gtInt, geInt, neInt, andInt, orInt, xorInt, shlInt, shrInt, ushrInt }));

		mOperatorProcs.addAll(intOperators);

		// Real operations
		// -------------------------------------------------------
		eqReal = new BoogieProcedure("$eqreal", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Eq, BoogieBaseTypes.getRealType()), mProgDec.getUniqueUid());
		neReal = new BoogieProcedure("$nereal", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Neq, BoogieBaseTypes.getRealType()), mProgDec.getUniqueUid());
		addReal = createProcedure("$addreal", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		subReal = createProcedure("$subreal", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		mulReal = createProcedure("$mulreal", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		divReal = createProcedure("$divreal", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		modReal = createProcedure("$modreal", BoogieBaseTypes.getRealType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		ltReal = createProcedure("$ltreal", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		leReal = createProcedure("$lereal", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		gtReal = createProcedure("$gtreal", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		geReal = createProcedure("$gereal", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		andReal = createProcedure("$andreal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		orReal = createProcedure("$orreal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		xorReal = createProcedure("$xorreal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		ushrReal = createProcedure("$ushrreal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		shlReal = createProcedure("$shlreal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());
		shrReal = createProcedure("$shrreal", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRealType(),
				BoogieBaseTypes.getRealType());

		realOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addReal, subReal, mulReal, divReal, modReal, eqReal, ltReal,
						leReal, gtReal, geReal, neReal, andReal, orReal, xorReal, shlReal, shrReal, ushrReal }));

		mOperatorProcs.addAll(realOperators);

		// Ref operations
		addRef = createProcedure("$addref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		subRef = createProcedure("$subref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		mulRef = createProcedure("$mulref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		divRef = createProcedure("$divref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		modRef = createProcedure("$modref", BoogieBaseTypes.getRefType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());

		eqRef = new BoogieProcedure("$eqref", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Eq, BoogieBaseTypes.getRefType()), mProgDec.getUniqueUid());
		neRef = new BoogieProcedure("$neref", BoogieBaseTypes.getBoolType(),
				createLogOpExpression(Operator.Neq, BoogieBaseTypes.getRefType()), mProgDec.getUniqueUid());

		ltRef = createProcedure("$ltref", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		leRef = createProcedure("$leref", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		gtRef = createProcedure("$gtref", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		geRef = createProcedure("$geref", BoogieBaseTypes.getBoolType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());

		andRef = createProcedure("$andref", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		orRef = createProcedure("$orref", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		xorRef = createProcedure("$xorref", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		ushrRef = createProcedure("$ushrref", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		shlRef = createProcedure("$shlref", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());
		shrRef = createProcedure("$shrref", BoogieBaseTypes.getIntType(), BoogieBaseTypes.getRefType(),
				BoogieBaseTypes.getRefType());

		refOperators = new LinkedList<BoogieProcedure>(
				Arrays.asList(new BoogieProcedure[] { addRef, subRef, mulRef, divRef, modRef, eqRef, ltRef, leRef,
						gtRef, geRef, neRef, andRef, orRef, xorRef, shlRef, shrRef, ushrRef }));

		mOperatorProcs.addAll(refOperators);

		// The cmp operators for real and ref are created in the end,
		// because they use other prelude functions
		cmpReal = new BoogieProcedure("$cmpreal", BoogieBaseTypes.getIntType(),
				createCmpExpression(BoogieBaseTypes.getRealType()), mProgDec.getUniqueUid());
		realOperators.add(cmpReal);
		mOperatorProcs.add(cmpReal);

		cmpRef = new BoogieProcedure("$cmpref", BoogieBaseTypes.getIntType(),
				createCmpExpression(BoogieBaseTypes.getRefType()), mProgDec.getUniqueUid());
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
		return this.newVariable;
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
			exp = createInvokeExpression(instanceofOp, args);
		} else {
			throw new UnsupportedOperationException("Operator not handled: " + op);
		}
		return exp;
	}

	private Expression getOperatorFun(String opcode, Expression l, Expression r) {
		LinkedList<BoogieProcedure> proctype = null;
		if (l.getType() == r.getType() && l.getType() == BoogieBaseTypes.getIntType()) {
			proctype = intOperators;
		} else if (l.getType() == r.getType() && l.getType() == BoogieBaseTypes.getRealType()) {
			proctype = realOperators;
		} else if (l.getType() instanceof BoogieObjectType && r.getType() instanceof BoogieObjectType) {
			proctype = refOperators;
		} else if (l.getType() == BoogieBaseTypes.getIntType() && r.getType() instanceof BoogieObjectType) {
			r = castToInt(r);
			proctype = intOperators;
		} else if (l.getType() instanceof BoogieObjectType && r.getType() == BoogieBaseTypes.getIntType()) {
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
		if (mHeapmode == HeapMode.SimpleHeap) {
			// BEGIN HACK : Our model checker doesn't understand functions with
			// bodies
			// well, we do equality and inequality inline to avoid the prelude
			if (opcode.compareTo("eq") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Eq, l, r);
				return ex;
			}

			if (opcode.compareTo("ne") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Neq, l, r);
				return ex;
			}

			if (opcode.compareTo("add") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Plus, l, r);
				return ex;
			}

			if (opcode.compareTo("sub") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Minus, l, r);
				return ex;
			}

			if (opcode.compareTo("mul") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Mul, l, r);
				return ex;
			}

			if (opcode.compareTo("div") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Div, l, r);
				return ex;
			}

			if (opcode.compareTo("ge") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Ge, l, r);
				return ex;
			}

			if (opcode.compareTo("le") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Le, l, r);
				return ex;
			}

			if (opcode.compareTo("lt") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Lt, l, r);
				return ex;
			}

			if (opcode.compareTo("gt") == 0) {
				BinOpExpression ex = new BinOpExpression(Operator.Gt, l, r);
				return ex;
			}
			// // END HACK
		}
		if (proc != null) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(l);
			args.add(r);
			InvokeExpression e = createInvokeExpression(proc, args);
			return e;
		}
		return null;
	}

	private Expression compareArrayEquality(Expression l, Expression r) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(l);
		args.add(r);
		if (l.getType() == BoogieBaseTypes.getIntArrType()) {
			return createInvokeExpression(eqIntArray, args);
		} else if (l.getType() == BoogieBaseTypes.getRealArrType()) {
			return createInvokeExpression(eqRealArray, args);
		} else if (l.getType() instanceof RefArrayType) {
			return createInvokeExpression(eqRefArray, args);
		} else if (l.getType() instanceof ArrArrayType) {
			mLogger.error("compareArrayEquality: CASE not implemented");
			return mProgDec.getFreshGlobalConstant(BoogieBaseTypes.getIntType());
		}
		mLogger.error("compareArrayEquality: Type not implemented");
		return mProgDec.getFreshGlobalConstant(BoogieBaseTypes.getIntType());
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

	public Expression createNegOp(Expression exp) {
		BoogieProcedure proc = null;
		if (exp.getType() == BoogieBaseTypes.getIntType()) {
			proc = negInt;
		} else if (exp.getType() == BoogieBaseTypes.getRealType()) {
			proc = negReal;
		} else if (exp.getType() instanceof BoogieObjectType) {
			proc = negRef;
		} else if (exp.getType() == BoogieBaseTypes.getBoolType()) {
			// Inline the negation operator for boolean expressions
			return new UnaryExpression(UnaryOperator.Not, exp);
		}
		if (proc != null) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			InvokeExpression e = createInvokeExpression(proc, args);
			return e;
		}
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

	public Expression castIfNecessary(Expression exp, BoogieType targetType) {
		if (compareTypes(exp.getType(), targetType)) {
			return exp;
		} else {
			if (targetType == BoogieBaseTypes.getIntType()) {
				return castToInt(exp);
			} else if (targetType == BoogieBaseTypes.getRealType()) {
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

	private Expression castToInt(Expression exp) {
		if (exp.getType() == BoogieBaseTypes.getIntType()) {
			return exp;
		} else if (exp.getType() == BoogieBaseTypes.getRealType()) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			return createInvokeExpression(realToInt, args);
		} else if (exp.getType() instanceof BoogieObjectType) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			return createInvokeExpression(refToInt, args);
		} else {
			return exp;
		}
	}

	private Expression castToReal(Expression exp) {
		if (exp.getType() == BoogieBaseTypes.getIntType()) {
			LinkedList<Expression> args = new LinkedList<Expression>();
			args.add(exp);
			return createInvokeExpression(intToReal, args);
		} else {
			return exp;
		}
	}

	private Expression castToArray(BoogieProgram prog, Expression exp, BoogieType arrtype) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		if (exp.getType() instanceof BoogieObjectType) {
			if (arrtype == BoogieBaseTypes.getIntArrType()) {
				return createInvokeExpression(refToIntArr, args);
			} else if (arrtype == BoogieBaseTypes.getRealArrType()) {
				return createInvokeExpression(refToRealArr, args);
			} else if (arrtype instanceof RefArrayType) {
				return createInvokeExpression(refToRefArr, args);
			} else if (arrtype instanceof ArrArrayType) {
				mLogger.error("castToArray: multiarrays are not really implemented");
				return mProgDec.getFreshGlobalConstant(arrtype);
			}
		}
		mLogger.error("castToArray: case is not implemented");
		mLogger.error("  cast from " + exp.getType().toString() + " to " + arrtype.toString());
		return mProgDec.getFreshGlobalConstant(arrtype);
	}

	private Expression castArrayToRef(BoogieProgram prog, Expression exp) {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(exp);
		BoogieType arrtype = exp.getType();
		if (arrtype == BoogieBaseTypes.getIntArrType()) {
			return createInvokeExpression(intArrToRef, args);
		} else if (arrtype == BoogieBaseTypes.getRealArrType()) {
			return createInvokeExpression(realArrToRef, args);
		} else if (arrtype instanceof RefArrayType) {
			return createInvokeExpression(refArrToRef, args);
		} else {
			mLogger.error("castToArray: case is not implemented");
			return mProgDec.getFreshGlobalConstant(BoogieBaseTypes.getRefType());
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

	public String toBoogie() {
		StringBuilder sb = new StringBuilder();

		if (mHeapmode == HeapMode.Default) {
			sb.append("// operator procedures ............\n");
			sb.append(negInt.toBoogie());
			sb.append(negReal.toBoogie());
			sb.append(negRef.toBoogie());

			sb.append(eqIntArray.toBoogie());
			sb.append(eqRealArray.toBoogie());
			sb.append(eqRefArray.toBoogie());

			sb.append("\n // Cast operators");
			sb.append(refToInt.toBoogie());
			sb.append(realToInt.toBoogie());
			sb.append(intToReal.toBoogie());

			sb.append(refArrToRef.toBoogie());
			sb.append(realArrToRef.toBoogie());
			sb.append(intArrToRef.toBoogie());

			sb.append(refToIntArr.toBoogie());
			sb.append(refToRealArr.toBoogie());
			sb.append(refToRefArr.toBoogie());

			sb.append(instanceofOp.toBoogie());
			// sb.append(lengthOp.toBoogie());

			sb.append(newVariable.toBoogie());

			for (BoogieProcedure proc : intOperators) {
				sb.append(proc.toBoogie());
			}
			for (BoogieProcedure proc : realOperators) {
				sb.append(proc.toBoogie());
			}
			for (BoogieProcedure proc : refOperators) {
				sb.append(proc.toBoogie());
			}
		}
		return sb.toString();
	}

	private Expression createBinOpExpression(BinOpExpression.Operator op, BoogieType t) {
		Variable x = mProgDec.createBoogieVariable("x", t, false);
		Variable y = mProgDec.createBoogieVariable("y", t, false);
		return new BinOpExpression(op, x, y);
	}

	private Expression createLogOpExpression(BinOpExpression.Operator op, BoogieType t) {
		Variable x = mProgDec.createBoogieVariable("x", t, false);
		Variable y = mProgDec.createBoogieVariable("y", t, false);
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
		final Variable x = mProgDec.createBoogieVariable("x", t, false);
		final Variable y = mProgDec.createBoogieVariable("y", t, false);

		if (t != BoogieBaseTypes.getIntType()) {
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
		Variable x = mProgDec.createBoogieVariable("x", BoogieBaseTypes.getIntType(), false);
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

	public HashSet<BoogieProcedure> getPreludeProcedures() {
		return this.mOperatorProcs;
	}

}
