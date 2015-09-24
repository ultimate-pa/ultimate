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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import org.joogie.HeapMode;
import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.InvokeStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieType;
import org.joogie.soot.factories.BoogieConstantFactory;
import org.joogie.soot.factories.BoogieTypeFactory;
import org.joogie.soot.factories.BoogieVariableFactory;
import org.joogie.soot.factories.OperatorFunctionFactory;
import org.joogie.util.Log;

import soot.Trap;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.BreakpointStmt;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NopStmt;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StmtSwitch;
import soot.jimple.TableSwitchStmt;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;

/**
 * @author schaef
 */
public class BoogieStmtSwitch implements StmtSwitch {

	private static final boolean SUPRESS_FALSE_POSITIVES = false;

	/*
	 * TODO: as you can see from the, this should be renamed. what it does is,
	 * when you have an ifthenelse, and you create an else block and the first
	 * statement of the else block is a jump target, we need to make sure that
	 * jump target and the assume from the else are in the same block. but as
	 * our iterator cannot see the next statement, we have to memorize it for
	 * one round in case of else statements.
	 */
	private BasicBlock elseBlockHack = null;

	/**
	 * 
	 */
	private BoogieProcedure currentProcedure = null;

	/**
	 * 
	 */
	private BasicBlock currentBlock = null;

	private HashMap<Stmt, BasicBlock> stmtBlockMap = new HashMap<Stmt, BasicBlock>();

	private BoogieValueSwitch valueSwitch = null;

	private boolean nextStmtIsNewBlock = true;

	private final HeapMode mHeapMode;

	public BoogieStmtSwitch(BoogieProcedure proc, HeapMode mode) {
		currentProcedure = proc;
		currentBlock = proc.getRootBlock(); // check if there is a rootblock
											// already (e.g., because exception
											// vars are initialized)
		valueSwitch = new BoogieValueSwitch(proc, this);

		// TODO: the current procedure should not be
		// kept in 2 different places. This causes bugs
		BoogieHelpers.currentProcedure = proc;
		mHeapMode = mode;
	}

	public void prepareCurrentBlock(Stmt stmt) {

		if (stmtBlockMap.containsKey(stmt)) {
			if (this.elseBlockHack != null && stmtBlockMap.get(stmt) != this.elseBlockHack) {
				// in that case, we created 2 blocks for the block and need to
				// merge them
				// not sure if this can happen
				for (BasicBlock b : new HashSet<BasicBlock>(this.elseBlockHack.Predecessors)) {
					b.disconnectFromSuccessor(this.elseBlockHack);
					b.connectToSuccessor(stmtBlockMap.get(stmt));
				}
				if (this.elseBlockHack.Successors.size() > 0) {
					throw new RuntimeException();
				}
				for (Statement s : this.elseBlockHack.getStatements()) {
					stmtBlockMap.get(stmt).addStatement(s, true);
				}
			} else {
				if (currentBlock != null)
					currentBlock.connectToSuccessor(stmtBlockMap.get(stmt));
			}
			currentBlock = stmtBlockMap.get(stmt);
		} else {
			// if there is a goto jumping to this stmt, it has to be a
			// separate block in the boogie program.
			if (nextStmtIsNewBlock || stmt.getBoxesPointingToThis().size() > 0) {
				nextStmtIsNewBlock = false;
				if (this.elseBlockHack == null) {
					BasicBlock nextBlock = new BasicBlock(BoogieHelpers.createLocationTag(stmt.getTags()));
					stmtBlockMap.put(stmt, nextBlock);
					if (currentBlock != null)
						currentBlock.connectToSuccessor(nextBlock);
					currentBlock = nextBlock;
				} else {
					stmtBlockMap.put(stmt, this.elseBlockHack);
					this.currentBlock = this.elseBlockHack;
				}
			}
		}
		elseBlockHack = null;
	}

	public BasicBlock getCurrentBlock() {
		return currentBlock;
	}

	private void addStatement(BasicBlock b, Statement s, boolean front) {
		for (Statement g : valueSwitch.getGuardingStatements()) {
			b.addStatement(g, front);
		}
		b.addStatement(s, front);
	}

	/*
	 * (non-Javadoc) used for both, AssignStmt and IdentityStmt
	 */
	private void translateAssigningStatement(Stmt st) {
		Expression lhs, rhs;
		Value rightVal;
		if (st instanceof DefinitionStmt) {
			DefinitionStmt arg0 = (DefinitionStmt) st;
			if (arg0.containsInvokeExpr() && arg0.getRightOp() instanceof InvokeExpr) {
				translateInvoke(arg0, arg0.getLeftOp(), (InvokeExpr) arg0.getRightOp());
				return;
			} else if (arg0.getRightOp() instanceof CaughtExceptionRef) {
				rightVal = arg0.getRightOp();
				rhs = GlobalsCache.v().getProcedureInfo(currentProcedure).findCatchVar(st);
				if (rhs == null) {
					Log.error("Catch block cannot be identified - skipping command");
					Log.error(arg0.toString());
					return;
				}
				arg0.getLeftOp().apply(valueSwitch);
				lhs = valueSwitch.getExpression();
			} else {
				rightVal = arg0.getRightOp();
				rightVal.apply(valueSwitch);
				rhs = valueSwitch.getExpression();
				arg0.getLeftOp().apply(valueSwitch);
				lhs = valueSwitch.getExpression();
			}
		} else if (st instanceof ReturnStmt || st instanceof RetStmt) {
			if (st instanceof ReturnStmt) {
				rightVal = ((ReturnStmt) st).getOp();
			} else {
				// TODO not tested yet!
				rightVal = ((RetStmt) st).getStmtAddress();
			}
			rightVal.apply(valueSwitch);
			rhs = valueSwitch.getExpression();
			lhs = currentProcedure.getReturnVariable();
		} else {
			Log.error("BoogieStmtSwitch.java: this is not an assignment!");
			return;
		}

		AssignStatement asgn = BoogieHelpers.createAssignment(lhs, rhs);
		asgn.setLocationTag(BoogieHelpers.createLocationTag(st.getTags()));
		addStatement(currentBlock, asgn, false);

		if (rightVal instanceof NewExpr) {
			addStatement(currentBlock, new AssumeStatement(BoogieHelpers.isNotNull(rhs)), false);
		} else if (rightVal instanceof NewArrayExpr) {

			Expression arrsize = BoogieProgram.v().getArraySizeExpression(rhs);
			if (arrsize != null) {
				NewArrayExpr narr = (NewArrayExpr) rightVal;
				narr.getSize().apply(valueSwitch);
				Expression narrsize = valueSwitch.getExpression();
				AssignStatement sizeasgn = BoogieHelpers.createAssignment(arrsize, narrsize);
				asgn.setLocationTag(BoogieHelpers.createLocationTag(st.getTags()));
				addStatement(currentBlock, sizeasgn, false);
				addStatement(currentBlock, new AssumeStatement(BoogieHelpers.isNotNull(rhs)), false);
			}
		} else if (rightVal instanceof NewMultiArrayExpr) {
			addStatement(currentBlock, new AssumeStatement(BoogieHelpers.isNotNull(rhs)), false);
		}
	}

	private void translateInvoke(Stmt st, Value assigns, InvokeExpr callExpr) {

		// java.lang.String.length is treated as a special case:
		if (callExpr.getMethod().getSignature().contains("<java.lang.String: int length()>") && assigns != null) {
			if (callExpr instanceof SpecialInvokeExpr) {
				((SpecialInvokeExpr) callExpr).getBase().apply(valueSwitch);
			} else if (callExpr instanceof VirtualInvokeExpr) {
				((VirtualInvokeExpr) callExpr).getBase().apply(valueSwitch);
			} else {
				// TODO: may report an error here?
				return;
			}
			Expression strExpr = valueSwitch.getExpression();
			Expression rhs = BoogieProgram.v().getStringLenExpression(strExpr);
			assigns.apply(valueSwitch);
			Expression lhs = valueSwitch.getExpression();
			addStatement(currentBlock, BoogieHelpers.createAssignment(lhs, rhs), false);
			return;
		}

		/*
		 * treat System.exit as a special case. Here: as a return, must be
		 * changed later.
		 */
		if (SUPRESS_FALSE_POSITIVES) {
			if (callExpr.getMethod().getSignature().contains("<java.lang.System: void exit(int)>")) {
				Log.info("Surppressing false positive from call to System.exit");
				currentBlock = null;
				nextStmtIsNewBlock = true;
				return;
			}
		}

		callExpr.apply(valueSwitch);
		Expression e = valueSwitch.getExpression();

		if (e instanceof InvokeExpression) {
			InvokeExpression ivk = (InvokeExpression) e;

			LinkedList<Expression> returntargets = new LinkedList<Expression>();
			ArrayList<Expression> exceptionvariables = new ArrayList<Expression>();

			BoogieProcedure proc = GlobalsCache.v().lookupProcedure(callExpr.getMethod(), mHeapMode);

			for (BoogieType t : GlobalsCache.v().getProcedureInfo(proc).getUncaughtExceptionTypes()) {
				Expression exp = GlobalsCache.v().getProcedureInfo(currentProcedure).lookupInvokeExceptionVar(t);
				returntargets.addLast(exp);
				exceptionvariables.add(exp);
			}

			if (assigns != null) {
				assigns.apply(valueSwitch);
				returntargets.addFirst(valueSwitch.getExpression());
			} else {
				if (proc.getReturnVariable() != null) {
					returntargets.addFirst(
							BoogieVariableFactory.v().getFreshLocalVariable(proc.getReturnVariable().getType()));
				}
			}
			InvokeStatement invoke = new InvokeStatement(ivk, returntargets);
			invoke.setLocationTag(BoogieHelpers.createLocationTag(st.getTags()));
			addStatement(currentBlock, invoke, false);

			// if
			// (GlobalsCache.v().getProcedureInfo(currentProcedure).getSootMethod().getSignature()
			// .contains("<terpword.ImageDialog: boolean validateControls()>")
			// && callExpr.getMethod().getSignature()
			// .contains("<java.lang.Integer: int parseInt(java.lang.String)>")
			// ) {
			// Log.debug("test everything");
			// }

			// TODO Warning, we have the information about which exception can
			// be thrown in two places: in exception variables and in the traps
			// of the procedure
			if (exceptionvariables.size() > 0) {
				LinkedList<Trap> traps = GlobalsCache.v().getProcedureInfo(currentProcedure).getAssociatedTrap(st);
				for (Expression exc : exceptionvariables) {
					// also check if the Trap catches this exception.

					BasicBlock catchBlock = new BasicBlock(currentBlock.getLocationTag());
					addStatement(catchBlock, new AssumeStatement(BoogieHelpers.isNotNull(exc)), true);
					translateExceptionHandling(catchBlock, traps, exc);
					currentBlock.connectToSuccessor(catchBlock);
					GlobalsCache.v().getProcedureInfo(currentProcedure).addExceptionBlock(catchBlock);

					BasicBlock nothrownBlock = new BasicBlock(currentBlock.getLocationTag());
					addStatement(nothrownBlock, new AssumeStatement(BoogieHelpers.isNull(exc)), true);
					currentBlock.connectToSuccessor(nothrownBlock);

					currentBlock = new BasicBlock(currentBlock.getLocationTag());
					nothrownBlock.connectToSuccessor(currentBlock);

				}

			}
		} else {
			assert(false);
		}
	}

	private void translateExceptionHandling(BasicBlock b, LinkedList<Trap> traps, Expression exception) {
		// Check if the trap is able to handle the exception
		for (Trap trap : traps) {
			if (trap != null && BoogieTypeFactory.compareTypes(((Variable) exception).getType(),
					BoogieTypeFactory.lookupBoogieType(trap.getException().getType())) <= 0) {
				// trap will handle the exception
				addStatement(b,
						BoogieHelpers.createAssignment(
								GlobalsCache.v().getProcedureInfo(currentProcedure).lookupLocalExceptionVar(trap),
								exception),
						false);
				BasicBlock catchblock = lookupBlock((Stmt) trap.getHandlerUnit());
				b.connectToSuccessor(catchblock);
				return;
			}
		}

		// The trap is not able to handle the exception, so the exception
		// has to be returned.
		Expression exret = currentProcedure.getExceptionalReturnVariable(exception.getType());
		BasicBlock retblock = new BasicBlock(b.getLocationTag());
		if (exret != null) {
			addStatement(retblock, BoogieHelpers.createAssignment(exret, exception), false);
		} else {
			Log.debug("translateExceptionHandling not fully implemented - does not affect soundness");
		}
		b.connectToSuccessor(retblock);

	}

	private void translateSwitchCase(Stmt s, Expression lhs, Expression rhs) {
		BasicBlock caseBlock = currentBlock;
		BasicBlock caseEnterBlock = new BasicBlock(BoogieHelpers.createLocationTag(s.getTags()));
		AssumeStatement asm = new AssumeStatement(OperatorFunctionFactory.v().createBinOp("==", lhs, rhs));
		asm.setLocationTag(BoogieHelpers.createLocationTag(s.getTags()));
		addStatement(caseEnterBlock, asm, true);
		caseBlock.connectToSuccessor(caseEnterBlock);
		caseEnterBlock.connectToSuccessor(lookupBlock(s));

		BasicBlock caseSkipBlock = new BasicBlock(BoogieHelpers.createLocationTag(s.getTags()));
		// TODO: warning, exp is actually not copied. In case we ever modify it,
		// we have to deepcopy!
		asm = new AssumeStatement(OperatorFunctionFactory.v().createBinOp("!=", lhs, rhs));
		asm.setLocationTag(BoogieHelpers.createLocationTag(s.getTags()));
		addStatement(caseSkipBlock, asm, true);
		caseBlock.connectToSuccessor(caseSkipBlock);
		currentBlock = new BasicBlock(BoogieHelpers.createLocationTag(s.getTags()));
		caseSkipBlock.connectToSuccessor(currentBlock);
	}

	private BasicBlock lookupBlock(Stmt stmt) {
		if (!stmtBlockMap.containsKey(stmt)) {
			BasicBlock b = new BasicBlock(BoogieHelpers.createLocationTag(stmt.getTags()));
			stmtBlockMap.put(stmt, b);
		}
		return stmtBlockMap.get(stmt);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseAssignStmt(soot.jimple.AssignStmt)
	 */
	@Override
	public void caseAssignStmt(AssignStmt arg0) {
		translateAssigningStatement(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.StmtSwitch#caseBreakpointStmt(soot.jimple.BreakpointStmt)
	 */
	@Override
	public void caseBreakpointStmt(BreakpointStmt arg0) {
		Log.error("Breakpoint: " + arg0.toString());
		assert(false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.StmtSwitch#caseEnterMonitorStmt(soot.jimple.EnterMonitorStmt)
	 * If this is only for synchronization, we don't need to translate it
	 */
	@Override
	public void caseEnterMonitorStmt(EnterMonitorStmt arg0) {
		// We do not consider multi threading right now
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.StmtSwitch#caseExitMonitorStmt(soot.jimple.ExitMonitorStmt)
	 * If this is only for synchronization, we don't need to translate it
	 */
	@Override
	public void caseExitMonitorStmt(ExitMonitorStmt arg0) {
		// We do not consider multi threading right now
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseGotoStmt(soot.jimple.GotoStmt)
	 */
	@Override
	public void caseGotoStmt(GotoStmt arg0) {
		BasicBlock targetBlock = lookupBlock((Stmt) arg0.getTarget());
		currentBlock.connectToSuccessor(targetBlock);
		currentBlock = null;
		nextStmtIsNewBlock = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseIdentityStmt(soot.jimple.IdentityStmt)
	 */
	@Override
	public void caseIdentityStmt(IdentityStmt arg0) {
		translateAssigningStatement(arg0);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseIfStmt(soot.jimple.IfStmt)
	 */
	@Override
	public void caseIfStmt(IfStmt arg0) {

		// Translate the conditional expression
		arg0.getCondition().apply(valueSwitch);
		Expression expr = valueSwitch.getExpression();

		// Create a new block which only contains the conditional
		BasicBlock conditional = lookupBlock((Stmt) arg0);
		if (conditional != currentBlock) {
			currentBlock.connectToSuccessor(conditional);
			currentBlock = conditional;
		}

		// Create a stub of the ThenBlock to be used later.
		BasicBlock thenConditionBlock = new BasicBlock(BoogieHelpers.createLocationTag(arg0.getTags()));
		currentBlock.connectToSuccessor(thenConditionBlock);

		AssumeStatement asm = new AssumeStatement(expr);
		asm.setLocationTag(BoogieHelpers.createLocationTag(arg0.getTags()));
		addStatement(thenConditionBlock, new AssumeStatement(expr), true);

		BasicBlock thenBlock = lookupBlock(arg0.getTarget());
		thenConditionBlock.connectToSuccessor(thenBlock);

		// TODO: WARNING this might break if there is a jump in the else block
		// (not sure if this is possible)
		// TODO: should be fixed? Test please
		BasicBlock elseBlock = new BasicBlock(BoogieHelpers.createLocationTag(arg0.getTags()));

		asm = new AssumeStatement(OperatorFunctionFactory.v().createNegOp(expr));
		asm.setLocationTag(BoogieHelpers.createLocationTag(arg0.getTags()));
		addStatement(elseBlock, asm, true);

		// this.elseBlockHack = elseBlock;

		currentBlock.connectToSuccessor(elseBlock);
		currentBlock = elseBlock;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseInvokeStmt(soot.jimple.InvokeStmt)
	 */
	@Override
	public void caseInvokeStmt(InvokeStmt arg0) {
		translateInvoke(arg0, null, arg0.getInvokeExpr());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.StmtSwitch#caseLookupSwitchStmt(soot.jimple.LookupSwitchStmt)
	 */
	@SuppressWarnings("rawtypes")
	@Override
	public void caseLookupSwitchStmt(LookupSwitchStmt arg0) {
		BasicBlock fanout = lookupBlock((Stmt) arg0);
		currentBlock.connectToSuccessor(fanout);
		currentBlock = fanout;

		arg0.getKey().apply(valueSwitch);
		Expression lhs = valueSwitch.getExpression();

		// create nested IfThenElse for Switch
		// WARNING: Only works because of a translation done by soot before.

		Iterator it = arg0.getLookupValues().iterator();
		int i = 0;
		while (it.hasNext()) {
			Stmt s = (Stmt) arg0.getTarget(i++);
			Expression rhs = BoogieConstantFactory.createConst((IntConstant) it.next());
			translateSwitchCase(s, lhs, rhs);
		}
		BasicBlock defaultBlock = lookupBlock((Stmt) arg0.getDefaultTarget());
		currentBlock.connectToSuccessor(defaultBlock);

		currentBlock = null;
		nextStmtIsNewBlock = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseNopStmt(soot.jimple.NopStmt)
	 */
	@Override
	public void caseNopStmt(NopStmt arg0) {
		// TODO Auto-generated method stub
		Log.error("NopStmt: " + arg0.toString());
		assert(false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseRetStmt(soot.jimple.RetStmt)
	 */
	@Override
	public void caseRetStmt(RetStmt arg0) {
		// TODO find testcase
		translateAssigningStatement(arg0);
		currentBlock = null;
		nextStmtIsNewBlock = true;
		assert(false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseReturnStmt(soot.jimple.ReturnStmt)
	 */
	@Override
	public void caseReturnStmt(ReturnStmt arg0) {
		translateAssigningStatement(arg0);
		currentBlock = null;
		nextStmtIsNewBlock = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.StmtSwitch#caseReturnVoidStmt(soot.jimple.ReturnVoidStmt)
	 */
	@Override
	public void caseReturnVoidStmt(ReturnVoidStmt arg0) {
		currentBlock = null;
		nextStmtIsNewBlock = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * soot.jimple.StmtSwitch#caseTableSwitchStmt(soot.jimple.TableSwitchStmt)
	 * The TableSwitch is a special case of the LookupSwitch, where all cases
	 * are consecutive.
	 */
	@Override
	public void caseTableSwitchStmt(TableSwitchStmt arg0) {
		BasicBlock fanout = lookupBlock((Stmt) arg0);

		currentBlock.connectToSuccessor(fanout);
		currentBlock = fanout;

		int lowidx = arg0.getLowIndex();
		int highidx = arg0.getHighIndex();

		arg0.getKey().apply(valueSwitch);
		Expression lhs = valueSwitch.getExpression();

		// create nested IfThenElse for Switch
		// WARNING: Only works because of a translation done by soot before.
		int counter = 0;
		for (int i = lowidx; i <= highidx; i++) {
			Stmt s = (Stmt) arg0.getTarget(counter++);
			Expression rhs = BoogieConstantFactory.createConst(i);
			translateSwitchCase(s, lhs, rhs);
		}

		BasicBlock defaultBlock = lookupBlock((Stmt) arg0.getDefaultTarget());
		currentBlock.connectToSuccessor(defaultBlock);

		currentBlock = null;
		nextStmtIsNewBlock = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#caseThrowStmt(soot.jimple.ThrowStmt)
	 */
	@Override
	public void caseThrowStmt(ThrowStmt arg0) {
		arg0.getOp().apply(valueSwitch);
		Expression e = valueSwitch.getExpression(); // this one contains the
													// variable the exception is
													// assigned to in the trap.
		LinkedList<Trap> traps = GlobalsCache.v().getProcedureInfo(currentProcedure).getAssociatedTrap(arg0);

		translateExceptionHandling(currentBlock, traps, e);

		currentBlock = null;
		nextStmtIsNewBlock = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.jimple.StmtSwitch#defaultCase(java.lang.Object)
	 */
	@Override
	public void defaultCase(Object arg0) {
		// TODO Auto-generated method stub
		assert(false);
	}

}
