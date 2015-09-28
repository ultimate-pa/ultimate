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
import org.joogie.boogie.constants.TypeExpression;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.soot.helper.BoogieProcedureInfo;
import org.joogie.soot.helper.BoogieProgramConstructionDecorator;
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

	private BoogieProcedure mCurrentProcedure;
	private Stack<Expression> mExpressionStack;

	private LinkedList<Statement> mGuardingStatements;
	private HeapMode mHeapMode;
	private BoogieProgramConstructionDecorator mProgDecl;

	public BoogieValueSwitch(BoogieProgramConstructionDecorator progDecl) {
		super();
		mProgDecl = progDecl;
		mCurrentProcedure = null;
		mExpressionStack = new Stack<Expression>();
		mGuardingStatements = new LinkedList<Statement>();
	}

	public LinkedList<Statement> getGuardingStatements() {
		LinkedList<Statement> ret = mGuardingStatements;
		mGuardingStatements = new LinkedList<Statement>();
		return ret;
	}

	private void assertNonNull(Expression e) {
		// TODO Replace assertion by throwing exception
		Expression guard = mProgDecl.getOperatorFunctionFactory().isNotNull(e);
		mGuardingStatements.add(new AssertStatement(guard));
	}

	private void assertInBounds(Expression e, Expression idx) {
		mGuardingStatements.add(new AssertStatement(mProgDecl.getOperatorFunctionFactory().createBinOp(">=", idx,
				mProgDecl.getConstantFactory().createConst(0))));
		Expression arrsize = mProgDecl.getProgram().getArraySizeExpression(e);
		if (arrsize != null) {
			mGuardingStatements
					.add(new AssertStatement(mProgDecl.getOperatorFunctionFactory().createBinOp("<", idx, arrsize)));
		}
	}

	public BoogieValueSwitch(BoogieProcedure proc, BoogieStmtSwitch stmtswitch) {
		mCurrentProcedure = proc;
		// TODO: the current procedure should not be
		// kept in 2 different places. This causes bugs
		mProgDecl.setCurrentProcedure(proc);
	}

	public Expression getExpression() {
		Expression e = mExpressionStack.pop();
		assert(mExpressionStack.isEmpty());
		return e;
	}

	private void translateBinOp(BinopExpr arg0) {
		arg0.getOp1().apply(this);
		arg0.getOp2().apply(this);

		Expression right = mExpressionStack.pop();
		Expression left = mExpressionStack.pop();
		mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().createBinOp(arg0.getSymbol(), left, right));

		if (arg0.getSymbol().contains(" / ") && right.getType() == BoogieBaseTypes.getIntType()) {
			this.mGuardingStatements.add(new AssertStatement(mProgDecl.getOperatorFunctionFactory().createBinOp("!=",
					right, mProgDecl.getConstantFactory().createConst(0))));
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
				thisvar = mProgDecl.getOperatorFunctionFactory().castIfNecessary(thisvar, BoogieBaseTypes.getRefType());
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

		BoogieProcedure callee = mProgDecl.getCache().lookupProcedure(arg0.getMethod(), mHeapMode);

		mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().createInvokeExpression(callee, args));
	}

	@Override
	public void caseClassConstant(ClassConstant arg0) {
		mExpressionStack.push(mProgDecl.getConstantFactory().createConst(arg0));
	}

	@Override
	public void caseDoubleConstant(DoubleConstant arg0) {
		mExpressionStack.push(mProgDecl.getConstantFactory().createConst(arg0));
	}

	@Override
	public void caseFloatConstant(FloatConstant arg0) {
		mExpressionStack.push(mProgDecl.getConstantFactory().createConst(arg0));
	}

	@Override
	public void caseIntConstant(IntConstant arg0) {
		mExpressionStack.push(mProgDecl.getConstantFactory().createConst(arg0));
	}

	@Override
	public void caseLongConstant(LongConstant arg0) {
		mExpressionStack.push(mProgDecl.getConstantFactory().createConst(arg0));
	}

	@Override
	public void caseNullConstant(NullConstant arg0) {
		mExpressionStack.push(mProgDecl.getProgram().getNullReference());
	}

	@Override
	public void caseStringConstant(StringConstant arg0) {
		Expression stringvar = mProgDecl.getConstantFactory().createConst(arg0);
		switch (mHeapMode) {
		case Default:
			mGuardingStatements.push(mProgDecl.getOperatorFunctionFactory().createAssignment(
					mProgDecl.getProgram().getStringLenExpression(stringvar),
					mProgDecl.getConstantFactory().createConst(arg0.value.length())));
			// TODO not sure, if this is the right place for this
			// actually, it should be handled during computation of modifies
			// clauses but then, it depends on the way we translate strings, so
			// this variable is actually not part of the original program
			mProgDecl.getCurrentProcedure().getModifiesGlobals().add(mProgDecl.getProgram().getStringSize());
			break;
		case SimpleHeap:
			// Just make sure the $stringSize array is not used.
		}
		mExpressionStack.push(stringvar);
	}

	@Override
	public void defaultCase(Object arg0) {
		Log.error("BoogieValueSwitch: case not covered");
		assert(false);
	}

	@Override
	public void caseAddExpr(AddExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseAndExpr(AndExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseCastExpr(CastExpr arg0) {
		Log.debug("Cast " + arg0.getOp().getType() + " to type " + arg0.getCastType() + " not implemented");
		arg0.getOp().apply(this);
	}

	@Override
	public void caseCmpExpr(CmpExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseCmpgExpr(CmpgExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseCmplExpr(CmplExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseDivExpr(DivExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseEqExpr(EqExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseGeExpr(GeExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseGtExpr(GtExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseInstanceOfExpr(InstanceOfExpr arg0) {
		arg0.getOp().apply(this);
		Expression te;
		if (arg0.getCheckType() instanceof RefType) {
			
			te = mProgDecl.getOperatorFunctionFactory().createBinOp("instanceof", getExpression(),
					new TypeExpression(mProgDecl.getCache().lookupTypeVariable((RefType) arg0.getCheckType())));
		} else {
			// arg0 checks an ArrayType not a RefType...
			Log.error("caseInstanceOfExpr is not fully implemented");
			te = mProgDecl.getFreshGlobalConstant(BoogieBaseTypes.getIntType());
		}
		mExpressionStack.add(te);
	}

	@Override
	public void caseInterfaceInvokeExpr(InterfaceInvokeExpr arg0) {
		translateInvokeExpr(arg0, arg0.getBase());
	}

	@Override
	public void caseLeExpr(LeExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseLengthExpr(LengthExpr arg0) {
		arg0.getOp().apply(this);
		Expression exp = this.getExpression();
		Expression lenexp = mProgDecl.getProgram().getArraySizeExpression(exp);
		if (lenexp == null) {
			Log.error(arg0.getOp().getType().toString());
			Log.error(">> " + exp.toBoogie() + " :: " + exp.getType().toBoogie());

			Log.error("BUG");
		}
		mExpressionStack.push(lenexp);
	}

	@Override
	public void caseLtExpr(LtExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseMulExpr(MulExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseNeExpr(NeExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseNegExpr(NegExpr arg0) {
		arg0.getOp().apply(this);
		mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().createNegOp(getExpression()));
	}

	@Override
	public void caseNewArrayExpr(NewArrayExpr arg0) {
		switch (mHeapMode) {
		case Default:
			mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().getFreshHeapField(arg0.getType()));
			break;
		case SimpleHeap:
			Log.error("Warning: Arrays are not supported by the theorem prover");
			Log.error("At: " + arg0);
			mExpressionStack.push(mProgDecl
					.getFreshGlobalConstant(mProgDecl.getTypeFactory().lookupBoogieType(arg0.getType())));
		}
	}

	@Override
	public void caseNewExpr(NewExpr arg0) {
		switch (mHeapMode) {
		case Default:
			mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().getFreshHeapField(arg0.getType()));
			break;
		case SimpleHeap:
			mExpressionStack.push(mProgDecl
					.getFreshGlobalConstant(mProgDecl.getTypeFactory().lookupBoogieType(arg0.getType())));
		}
	}

	@Override
	public void caseNewMultiArrayExpr(NewMultiArrayExpr arg0) {
		switch (mHeapMode) {
		case Default:
			mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().getFreshHeapField(arg0.getType()));
			break;
		case SimpleHeap:
			Log.error("Warning: Multiarrays are not supported by the theorem prover.");
			Log.error("At: " + arg0);
			mExpressionStack.push(mProgDecl
					.getFreshGlobalConstant(mProgDecl.getTypeFactory().lookupBoogieType(arg0.getType())));
		}
	}

	@Override
	public void caseOrExpr(OrExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseRemExpr(RemExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseShlExpr(ShlExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseShrExpr(ShrExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseSpecialInvokeExpr(SpecialInvokeExpr arg0) {
		translateInvokeExpr(arg0, arg0.getBase());
	}

	@Override
	public void caseStaticInvokeExpr(StaticInvokeExpr arg0) {
		translateInvokeExpr(arg0, null);
	}

	@Override
	public void caseSubExpr(SubExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseUshrExpr(UshrExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseVirtualInvokeExpr(VirtualInvokeExpr arg0) {
		translateInvokeExpr(arg0, arg0.getBase());
	}

	@Override
	public void caseDynamicInvokeExpr(DynamicInvokeExpr arg0) {
		// TODO This method has not been tested
		translateInvokeExpr(arg0, null);
	}

	@Override
	public void caseXorExpr(XorExpr arg0) {
		translateBinOp(arg0);
	}

	@Override
	public void caseArrayRef(ArrayRef arg0) {
		arg0.getBase().apply(this);
		Expression arr = this.getExpression();
		arg0.getIndex().apply(this);
		Expression idx = this.getExpression();
		// TODO Replace assertion by throwing exceptions
		assertInBounds(arr, idx);
		mExpressionStack.push(new ArrayReadExpression(arr, idx));
	}

	@Override
	public void caseCaughtExceptionRef(CaughtExceptionRef arg0) {
		Log.error("THIS CASE MUST BE HANDELED IN STMTSWITCH!");
	}

	@Override
	public void caseInstanceFieldRef(InstanceFieldRef arg0) {
		switch (mHeapMode) {
		case Default:
			arg0.getBase().apply(this);
			Expression instance = this.getExpression();
			assertNonNull(instance);
			mExpressionStack.push(mProgDecl.getOperatorFunctionFactory().createSimpleHeapAccess(instance,
					mProgDecl.getCache().lookupField(arg0.getField())));
			break;
		case SimpleHeap:
			// Do a static reference
			mExpressionStack.push(mProgDecl.getCache().lookupStaticField(arg0.getField()));
		}
	}

	@Override
	public void caseParameterRef(ParameterRef arg0) {
		mExpressionStack.push(mCurrentProcedure.lookupParameter(arg0.getIndex()));
	}

	@Override
	public void caseStaticFieldRef(StaticFieldRef arg0) {
		mExpressionStack.push(mProgDecl.getCache().lookupStaticField(arg0.getField()));
	}

	@Override
	public void caseThisRef(ThisRef arg0) {
		mExpressionStack.push(mCurrentProcedure.getThisVariable());
	}

	@Override
	public void caseLocal(Local arg0) {
		BoogieProcedureInfo info = mProgDecl.getCache().getProcedureInfo(this.mCurrentProcedure);
		mExpressionStack.push(info.lookupLocal(arg0));
	}

	@Override
	public void caseMethodHandle(MethodHandle arg0) {
		// SAF: 07.07.15 updated to newest soot
		throw new RuntimeException("MethodHandle not implemented");
	}

}
