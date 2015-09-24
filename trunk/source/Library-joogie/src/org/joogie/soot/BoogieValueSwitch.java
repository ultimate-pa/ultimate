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

package org.joogie.soot;

import java.util.LinkedList;
import java.util.Stack;

import org.joogie.HeapMode;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.constants.TypeExpression;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.soot.factories.BoogieConstantFactory;
import org.joogie.soot.factories.BoogieTypeFactory;
import org.joogie.soot.factories.BoogieVariableFactory;
import org.joogie.soot.factories.OperatorFunctionFactory;
import org.joogie.util.Log;

import soot.Local;
import soot.RefType;
import soot.Value;
import soot.jimple.AddExpr;
import soot.jimple.AndExpr;
import soot.jimple.ArrayRef;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.ClassConstant;
import soot.jimple.CmpExpr;
import soot.jimple.CmpgExpr;
import soot.jimple.CmplExpr;
import soot.jimple.DivExpr;
import soot.jimple.DoubleConstant;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.EqExpr;
import soot.jimple.FloatConstant;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.JimpleValueSwitch;
import soot.jimple.LeExpr;
import soot.jimple.LengthExpr;
import soot.jimple.LongConstant;
import soot.jimple.LtExpr;
import soot.jimple.MethodHandle;
import soot.jimple.MulExpr;
import soot.jimple.NeExpr;
import soot.jimple.NegExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.OrExpr;
import soot.jimple.ParameterRef;
import soot.jimple.RemExpr;
import soot.jimple.ShlExpr;
import soot.jimple.ShrExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.StringConstant;
import soot.jimple.SubExpr;
import soot.jimple.ThisRef;
import soot.jimple.UshrExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.XorExpr;

/**
 * @author schaef
 */
public class BoogieValueSwitch implements JimpleValueSwitch {

	private BoogieProcedure currentProcedure = null;
	private Stack<Expression> expressionStack = new Stack<Expression>();

	private LinkedList<Statement> guardingStatements = new LinkedList<Statement>();
	private HeapMode mHeapMode;

	public LinkedList<Statement> getGuardingStatements() {
		LinkedList<Statement> ret = guardingStatements;
		guardingStatements = new LinkedList<Statement>();
		return ret;
	}

	private void assertNonNull(Expression e) {
		// TODO Replace assertion by throwing exception
		Expression guard = BoogieHelpers.isNotNull(e);
		guardingStatements.add(new AssertStatement(guard));
	}

	private void assertInBounds(Expression e, Expression idx) {
		guardingStatements.add(new AssertStatement(
				OperatorFunctionFactory.v().createBinOp(">=", idx, BoogieConstantFactory.createConst(0))));
		Expression arrsize = BoogieProgram.v().getArraySizeExpression(e);
		if (arrsize != null) {
			guardingStatements.add(new AssertStatement(OperatorFunctionFactory.v().createBinOp("<", idx, arrsize)));
		}
	}

	public BoogieValueSwitch(BoogieProcedure proc, BoogieStmtSwitch stmtswitch) {
		currentProcedure = proc;
		// TODO: the current procedure should not be
		// kept in 2 different places. This causes bugs
		BoogieHelpers.currentProcedure = proc;
	}

	public Expression getExpression() {
		Expression e = expressionStack.pop();
		assert(expressionStack.isEmpty());
		return e;
	}

	private void translateBinOp(BinopExpr arg0) {
		arg0.getOp1().apply(this);
		arg0.getOp2().apply(this);

		Expression right = expressionStack.pop();
		Expression left = expressionStack.pop();
		expressionStack.push(OperatorFunctionFactory.v().createBinOp(arg0.getSymbol(), left, right));

		if (arg0.getSymbol().contains(" / ") && right.getType() == BoogieBaseTypes.getIntType()) {
			this.guardingStatements.add(new AssertStatement(
					OperatorFunctionFactory.v().createBinOp("!=", right, BoogieConstantFactory.createConst(0))));
		}

	}

	private void translateInvokeExpr(InvokeExpr arg0, Value base) {
		LinkedList<Expression> args = new LinkedList<Expression>();

		if (base != null) {
			// If method is not static, give the instance of the base class as
			// first arg
			base.apply(this);
			Expression thisvar = this.getExpression();

			if (!(thisvar.getType() instanceof BoogieObjectType)) {
				// if the this var is not a reference we do a brute force cast
				// this is a hack but should be sound
				Log.error("WARNING - more testing requried for translateInvokeExpr");
				thisvar = OperatorFunctionFactory.v().castIfNecessary(thisvar, BoogieBaseTypes.getRefType());
			}

			assertNonNull(thisvar);
			args.add(thisvar);

			// this identifies a call in argoUML that caused problems
			// if (arg0.getMethod().getNumber()==35 &&
			// arg0.getMethod().getName().contains("clone")) {
			// Log.error("");
			// }

		}
		for (int i = 0; i < arg0.getArgCount(); i++) {
			arg0.getArg(i).apply(this);
			args.addLast(this.getExpression());
		}

		BoogieProcedure callee = GlobalsCache.v().lookupProcedure(arg0.getMethod(), mHeapMode);

		expressionStack.push(BoogieHelpers.createInvokeExpression(callee, args));
	}

	// private void tmp_pushEmptyConstant() {
	// Expression c = new Constant();
	// expressionStack.push(c);
	// }

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ConstantSwitch#caseClassConstant(soot.jimple.ClassConstant)
	 */
	@Override
	public void caseClassConstant(ClassConstant arg0) {
		expressionStack.push(BoogieConstantFactory.createConst(arg0));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ConstantSwitch#caseDoubleConstant(soot.jimple.DoubleConstant)
	 */
	@Override
	public void caseDoubleConstant(DoubleConstant arg0) {
		expressionStack.push(BoogieConstantFactory.createConst(arg0));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ConstantSwitch#caseFloatConstant(soot.jimple.FloatConstant)
	 */
	@Override
	public void caseFloatConstant(FloatConstant arg0) {
		expressionStack.push(BoogieConstantFactory.createConst(arg0));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ConstantSwitch#caseIntConstant(soot.jimple.IntConstant)
	 */
	@Override
	public void caseIntConstant(IntConstant arg0) {
		expressionStack.push(BoogieConstantFactory.createConst(arg0));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ConstantSwitch#caseLongConstant(soot.jimple.LongConstant)
	 */
	@Override
	public void caseLongConstant(LongConstant arg0) {
		expressionStack.push(BoogieConstantFactory.createConst(arg0));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ConstantSwitch#caseNullConstant(soot.jimple.NullConstant)
	 */
	@Override
	public void caseNullConstant(NullConstant arg0) {
		expressionStack.push(BoogieProgram.v().getNullReference());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ConstantSwitch#caseStringConstant(soot.jimple.StringConstant)
	 */
	@Override
	public void caseStringConstant(StringConstant arg0) {
		Expression stringvar = BoogieConstantFactory.createConst(arg0);
		switch (mHeapMode) {
		case Default:
			guardingStatements.push(BoogieHelpers.createAssignment(BoogieProgram.v().getStringLenExpression(stringvar),
					BoogieConstantFactory.createConst(arg0.value.length())));
			// TODO not sure, if this is the right place for this
			// actually, it should be handled during computation of modifies
			// clauses but then, it depends on the way we translate strings, so
			// this variable is actually not part of the original program
			BoogieHelpers.currentProcedure.modifiesGlobals.add(BoogieProgram.v().stringSize);
			break;
		case SimpleHeap:
			// Just make sure the $stringSize array is not used.
		}
		expressionStack.push(stringvar);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ConstantSwitch#defaultCase(java.lang.Object)
	 */
	@Override
	public void defaultCase(Object arg0) {
		Log.error("BoogieValueSwitch: case not covered");
		assert(false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseAddExpr(soot.jimple.AddExpr)
	 */
	@Override
	public void caseAddExpr(AddExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseAndExpr(soot.jimple.AndExpr)
	 */
	@Override
	public void caseAndExpr(AndExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseCastExpr(soot.jimple.CastExpr)
	 */
	@Override
	public void caseCastExpr(CastExpr arg0) {
		Log.debug("Cast " + arg0.getOp().getType() + " to type " + arg0.getCastType() + " not implemented");
		arg0.getOp().apply(this);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseCmpExpr(soot.jimple.CmpExpr)
	 */
	@Override
	public void caseCmpExpr(CmpExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseCmpgExpr(soot.jimple.CmpgExpr)
	 */
	@Override
	public void caseCmpgExpr(CmpgExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseCmplExpr(soot.jimple.CmplExpr)
	 */
	@Override
	public void caseCmplExpr(CmplExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseDivExpr(soot.jimple.DivExpr)
	 */
	@Override
	public void caseDivExpr(DivExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseEqExpr(soot.jimple.EqExpr)
	 */
	@Override
	public void caseEqExpr(EqExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseGeExpr(soot.jimple.GeExpr)
	 */
	@Override
	public void caseGeExpr(GeExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseGtExpr(soot.jimple.GtExpr)
	 */
	@Override
	public void caseGtExpr(GtExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ExprSwitch#caseInstanceOfExpr(soot.jimple.InstanceOfExpr)
	 */
	@Override
	public void caseInstanceOfExpr(InstanceOfExpr arg0) {
		arg0.getOp().apply(this);
		Expression te;
		if (arg0.getCheckType() instanceof RefType) {
			te = OperatorFunctionFactory.v().createBinOp("instanceof", getExpression(),
					new TypeExpression(GlobalsCache.v().lookupTypeVariable((RefType) arg0.getCheckType())));
		} else {
			// arg0 checks an ArrayType not a RefType...
			Log.error("caseInstanceOfExpr is not fully implemented");
			te = BoogieVariableFactory.v().getFreshGlobalConstant(BoogieBaseTypes.getIntType());
		}
		expressionStack.add(te);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseInterfaceInvokeExpr(soot.jimple.
	 * InterfaceInvokeExpr)
	 */
	@Override
	public void caseInterfaceInvokeExpr(InterfaceInvokeExpr arg0) {
		translateInvokeExpr(arg0, arg0.getBase());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseLeExpr(soot.jimple.LeExpr)
	 */
	@Override
	public void caseLeExpr(LeExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseLengthExpr(soot.jimple.LengthExpr)
	 */
	@Override
	public void caseLengthExpr(LengthExpr arg0) {
		arg0.getOp().apply(this);
		Expression exp = this.getExpression();
		Expression lenexp = BoogieProgram.v().getArraySizeExpression(exp);
		if (lenexp == null) {
			Log.error(arg0.getOp().getType().toString());
			Log.error(">> " + exp.toBoogie() + " :: " + exp.getType().toBoogie());

			Log.error("BUG");
		}
		expressionStack.push(lenexp);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseLtExpr(soot.jimple.LtExpr)
	 */
	@Override
	public void caseLtExpr(LtExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseMulExpr(soot.jimple.MulExpr)
	 */
	@Override
	public void caseMulExpr(MulExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseNeExpr(soot.jimple.NeExpr)
	 */
	@Override
	public void caseNeExpr(NeExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseNegExpr(soot.jimple.NegExpr)
	 */
	@Override
	public void caseNegExpr(NegExpr arg0) {
		arg0.getOp().apply(this);
		expressionStack.push(OperatorFunctionFactory.v().createNegOp(getExpression()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseNewArrayExpr(soot.jimple.NewArrayExpr)
	 */
	@Override
	public void caseNewArrayExpr(NewArrayExpr arg0) {
		switch (mHeapMode) {
		case Default:
			expressionStack.push(BoogieVariableFactory.v().getFreshHeapField(arg0.getType()));
			break;
		case SimpleHeap:
			Log.error("Warning: Arrays are not supported by the theorem prover");
			Log.error("At: " + arg0);
			expressionStack.push(BoogieVariableFactory.v()
					.getFreshGlobalConstant(BoogieTypeFactory.lookupBoogieType(arg0.getType())));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseNewExpr(soot.jimple.NewExpr)
	 */
	@Override
	public void caseNewExpr(NewExpr arg0) {
		switch (mHeapMode) {
		case Default:
			expressionStack.push(BoogieVariableFactory.v().getFreshHeapField(arg0.getType()));
			break;
		case SimpleHeap:
			expressionStack.push(BoogieVariableFactory.v()
					.getFreshGlobalConstant(BoogieTypeFactory.lookupBoogieType(arg0.getType())));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseNewMultiArrayExpr(soot.jimple.
	 * NewMultiArrayExpr )
	 */
	@Override
	public void caseNewMultiArrayExpr(NewMultiArrayExpr arg0) {
		switch (mHeapMode) {
		case Default:
			expressionStack.push(BoogieVariableFactory.v().getFreshHeapField(arg0.getType()));
			break;
		case SimpleHeap:
			Log.error("Warning: Multiarrays are not supported by the theorem prover.");
			Log.error("At: " + arg0);
			expressionStack.push(BoogieVariableFactory.v()
					.getFreshGlobalConstant(BoogieTypeFactory.lookupBoogieType(arg0.getType())));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseOrExpr(soot.jimple.OrExpr)
	 */
	@Override
	public void caseOrExpr(OrExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseRemExpr(soot.jimple.RemExpr)
	 */
	@Override
	public void caseRemExpr(RemExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseShlExpr(soot.jimple.ShlExpr)
	 */
	@Override
	public void caseShlExpr(ShlExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseShrExpr(soot.jimple.ShrExpr)
	 */
	@Override
	public void caseShrExpr(ShrExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseSpecialInvokeExpr(soot.jimple.
	 * SpecialInvokeExpr )
	 */
	@Override
	public void caseSpecialInvokeExpr(SpecialInvokeExpr arg0) {
		translateInvokeExpr(arg0, arg0.getBase());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.ExprSwitch#caseStaticInvokeExpr(soot.jimple.StaticInvokeExpr)
	 */
	@Override
	public void caseStaticInvokeExpr(StaticInvokeExpr arg0) {
		translateInvokeExpr(arg0, null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseSubExpr(soot.jimple.SubExpr)
	 */
	@Override
	public void caseSubExpr(SubExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseUshrExpr(soot.jimple.UshrExpr)
	 */
	@Override
	public void caseUshrExpr(UshrExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseVirtualInvokeExpr(soot.jimple.
	 * VirtualInvokeExpr )
	 */
	@Override
	public void caseVirtualInvokeExpr(VirtualInvokeExpr arg0) {
		translateInvokeExpr(arg0, arg0.getBase());
	}

	@Override
	public void caseDynamicInvokeExpr(DynamicInvokeExpr arg0) {
		// TODO This method has not been tested
		translateInvokeExpr(arg0, null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.ExprSwitch#caseXorExpr(soot.jimple.XorExpr)
	 */
	@Override
	public void caseXorExpr(XorExpr arg0) {
		translateBinOp(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.RefSwitch#caseArrayRef(soot.jimple.ArrayRef)
	 */
	@Override
	public void caseArrayRef(ArrayRef arg0) {
		arg0.getBase().apply(this);
		Expression arr = this.getExpression();
		arg0.getIndex().apply(this);
		Expression idx = this.getExpression();
		// TODO Replace assertion by throwing exceptions
		assertInBounds(arr, idx);
		expressionStack.push(new ArrayReadExpression(arr, idx));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.RefSwitch#caseCaughtExceptionRef(soot.jimple.
	 * CaughtExceptionRef )
	 */
	@Override
	public void caseCaughtExceptionRef(CaughtExceptionRef arg0) {
		Log.error("THIS CASE MUST BE HANDELED IN STMTSWITCH!");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.RefSwitch#caseInstanceFieldRef(soot.jimple.InstanceFieldRef)
	 */
	@Override
	public void caseInstanceFieldRef(InstanceFieldRef arg0) {
		switch (mHeapMode) {
		case Default:
			arg0.getBase().apply(this);
			Expression instance = this.getExpression();
			assertNonNull(instance);
			expressionStack.push(OperatorFunctionFactory.v().createSimpleHeapAccess(instance,
					GlobalsCache.v().lookupField(arg0.getField())));
			break;
		case SimpleHeap:
			// Do a static reference
			expressionStack.push(GlobalsCache.v().lookupStaticField(arg0.getField()));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.RefSwitch#caseParameterRef(soot.jimple.ParameterRef)
	 */
	@Override
	public void caseParameterRef(ParameterRef arg0) {
		expressionStack.push(currentProcedure.lookupParameter(arg0.getIndex()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.RefSwitch#caseStaticFieldRef(soot.jimple.StaticFieldRef)
	 */
	@Override
	public void caseStaticFieldRef(StaticFieldRef arg0) {
		expressionStack.push(GlobalsCache.v().lookupStaticField(arg0.getField()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.RefSwitch#caseThisRef(soot.jimple.ThisRef)
	 */
	@Override
	public void caseThisRef(ThisRef arg0) {
		expressionStack.push(currentProcedure.getThisVariable());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.JimpleValueSwitch#caseLocal(soot.Local)
	 */
	@Override
	public void caseLocal(Local arg0) {
		BoogieProcedureInfo info = GlobalsCache.v().getProcedureInfo(this.currentProcedure);
		expressionStack.push(info.lookupLocal(arg0));
	}

	@Override
	public void caseMethodHandle(MethodHandle arg0) {
		// SAF: 07.07.15 updated to newest soot
		throw new RuntimeException("MethodHandle not implemented");
	}

}
