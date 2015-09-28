/**
 * 
 */
package org.joogie.soot.helper;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.types.BoogieType;

import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Trap;
import soot.jimple.Stmt;

/**
 * @author schaef
 *
 */
public class BoogieProcedureInfo {

	private final BoogieProcedure mProcedure;
	private final SootMethod mSootMethod;
	private final Map<Local, Variable> mLocalMap;

	// < Exception handling variables --------------------------------
	private final Set<Trap> mProcedureTraps;
	private final Map<Stmt, LinkedList<Trap>> mCatchBlocks;
	// Variable for exceptions handled in catch blocks
	private final Map<Trap, Expression> mCaughtExceptionVars;
	// Variables for exceptions that might be returned by invoked methods
	private final Map<BoogieType, Expression> mInvokeExceptionVars;
	// -->
	private final Set<BasicBlock> mExceptionBlocks;
	private final BoogieProgramConstructionDecorator mProgDecl;

	public BoogieProcedureInfo(BoogieProgramConstructionDecorator progDecl, BoogieProcedure proc, SootMethod method) {
		mProcedure = proc;
		mSootMethod = method;
		mProgDecl = progDecl;

		mLocalMap = new HashMap<Local, Variable>();
		mCatchBlocks = new HashMap<Stmt, LinkedList<Trap>>();
		mCaughtExceptionVars = new HashMap<Trap, Expression>();
		mInvokeExceptionVars = new HashMap<BoogieType, Expression>();
		mExceptionBlocks = new HashSet<BasicBlock>();

		if (mSootMethod.hasActiveBody()) {
			Body b = mSootMethod.getActiveBody();
			// we have to create the unit graph, otherwise b.getTraps crashes
			// new ExceptionalUnitGraph(b);
			mProcedureTraps = new HashSet<Trap>(b.getTraps());
		} else {
			mProcedureTraps = null;
		}
	}

	public BoogieProcedure getBoogieProcedure() {
		return this.mProcedure;
	}

	public SootMethod getSootMethod() {
		return this.mSootMethod;
	}

	public Variable lookupLocal(Local local) {
		if (!mLocalMap.containsKey(local)) {
			Variable v = mProgDecl.createLocalVar(local);
			mLocalMap.put(local, v);
			this.mProcedure.addLocal(v);
		}
		return mLocalMap.get(local);
	}

	public Map<Local, Variable> getLocalMap() {
		return mLocalMap;
	}

	/*
	 * Exception handling procedures
	 */
	public Set<Trap> getTraps() {
		return mProcedureTraps;
	}

	public LinkedList<Trap> getAssociatedTrap(Stmt stmt) {
		LinkedList<Trap> traps = new LinkedList<Trap>();
		if (mCatchBlocks.containsKey(stmt)) {
			traps.addAll(mCatchBlocks.get(stmt));
		}
		return traps;
	}

	public void addCaughtException(Stmt stmt, Trap t) {
		if (!mCatchBlocks.containsKey(stmt)) {
			LinkedList<Trap> traps = new LinkedList<Trap>();
			mCatchBlocks.put(stmt, traps);
			mProcedureTraps.add(t);
		}
		mCatchBlocks.get(stmt).add(t);
	}

	public void addUncaughtException(BoogieType t) {
		Expression exv = this.mProcedure.getExceptionalReturnVariable(t);
		if (null == exv) {
			mProcedure.addExceptionalReturnVariable(t, mProgDecl.getFreshLocalVariable("$Exep", t));
			AssignStatement initvar = mProgDecl.getOperatorFunctionFactory()
					.createAssignment(this.mProcedure.getExceptionalReturnVariable(t), mProgDecl.getNullVariable());
			BasicBlock rootBlock = mProcedure.getRootBlock();
			if (rootBlock == null) {
				rootBlock = mProgDecl.createBasicBlock(mProcedure);
				mProcedure.setBodyRoot(rootBlock);
			}
			rootBlock.addStatement(initvar, true);
		}
	}

	public Expression findCatchVar(Stmt arg0) {
		for (Trap t : mProcedureTraps) {
			if (t.getHandlerUnit() == arg0) {
				return this.lookupLocalExceptionVar(t);
			} else {
				// Log.error("NOT: "+(t.getHandlerUnit()).toString());
			}
		}
		return null;
	}

	public Expression lookupLocalExceptionVar(Trap t) {

		if (!mCaughtExceptionVars.containsKey(t)) {
			BoogieType type = mProgDecl.getTypeFactory().lookupBoogieType(t.getException().getType());
			mCaughtExceptionVars.put(t, mProgDecl.getFreshLocalVariable("$caughtEx", type));
			AssignStatement initvar = mProgDecl.getOperatorFunctionFactory()
					.createAssignment(mCaughtExceptionVars.get(t), mProgDecl.getNullVariable());
			BasicBlock rootBlock = mProcedure.getRootBlock();
			if (rootBlock == null) {
				rootBlock = mProgDecl.createBasicBlock(mProcedure);
			}
			rootBlock.addStatement(initvar, true);
		}
		return mCaughtExceptionVars.get(t);
	}

	public Expression lookupInvokeExceptionVar(BoogieType t) {

		if (!mInvokeExceptionVars.containsKey(t)) {
			mInvokeExceptionVars.put(t, mProgDecl.getFreshLocalVariable("$caughtEx", t));
			AssignStatement initvar = mProgDecl.getOperatorFunctionFactory()
					.createAssignment(mInvokeExceptionVars.get(t), mProgDecl.getNullVariable());
			BasicBlock rootBlock = this.mProcedure.getRootBlock();
			if (rootBlock == null) {
				rootBlock = mProgDecl.createBasicBlock(mProcedure);
			}
			rootBlock.addStatement(initvar, true);
		}
		return mInvokeExceptionVars.get(t);
	}

	// TODO: this must not be a set because
	// the order is important when generating the variables
	// for a procedure call.
	public Set<BoogieType> getUncaughtExceptionTypes() {
		return this.mProcedure.getUncaughtTypes();
	}

	public void addExceptionBlock(BasicBlock catchBlock) {
		this.mExceptionBlocks.add(catchBlock);
	}

	/**
	 * @return the exceptionBlocks
	 */
	public Set<BasicBlock> getExceptionBlocks() {
		return mExceptionBlocks;
	}

}
