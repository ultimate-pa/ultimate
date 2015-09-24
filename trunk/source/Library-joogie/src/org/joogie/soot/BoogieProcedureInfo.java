/**
 * 
 */
package org.joogie.soot;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.types.BoogieType;
import org.joogie.soot.factories.BoogieTypeFactory;
import org.joogie.soot.factories.BoogieVariableFactory;

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
	
	private BoogieProcedure boogieProcedure=null;
	private SootMethod sootMethod=null;	
	private HashMap<Local, Variable> localMap = new HashMap<Local, Variable>();
	
	// < Exception handling variables --------------------------------
	private HashSet<Trap> procedureTraps = null;
	private HashMap<Stmt, LinkedList<Trap>> catchBlocks = new HashMap<Stmt, LinkedList<Trap>>();
	// Variable for exceptions handled in catch blocks
	private HashMap<Trap, Expression> caughtExceptionVars = new HashMap<Trap, Expression>();
	// Variables for exceptions that might be returned by invoked methods
	private HashMap<BoogieType, Expression> invokeExceptionVars = new HashMap<BoogieType, Expression>();
	// -->
	private HashSet<BasicBlock> exceptionBlocks = new HashSet<BasicBlock>();
	
	public BoogieProcedureInfo(BoogieProcedure proc, SootMethod method) {
		this.boogieProcedure = proc;
		this.sootMethod = method;

		if (sootMethod.hasActiveBody()) {
			Body b = sootMethod.getActiveBody();
			//we have to create the unit graph, otherwise b.getTraps crashes
			//new ExceptionalUnitGraph(b);
			procedureTraps = new HashSet<Trap>(b.getTraps());
		}
	}

	public BoogieProcedure getBoogieProcedure() {
		return this.boogieProcedure;
	}
	
	public SootMethod getSootMethod() {
		return this.sootMethod;
	}
	
	public Variable lookupLocal(Local local) {
		if (!localMap.containsKey(local)) {
			Variable v = BoogieHelpers.createLocalVar(local);
			localMap.put(local, v);
			this.boogieProcedure.addLocal(v);
		}
		return localMap.get(local);
	}

	public HashMap<Local, Variable> getLocalMap() {
		return localMap;
	}
/*
 * Exception handling procedures
 */
	public Set<Trap> getTraps() {
		return procedureTraps;
	}

	public LinkedList<Trap> getAssociatedTrap(Stmt stmt) {
		LinkedList<Trap> traps = new LinkedList<Trap>();
		if (catchBlocks.containsKey(stmt)) {
			traps.addAll(catchBlocks.get(stmt));
		}
		return traps;
	}

	public void addCaughtException(Stmt stmt, Trap t) {
		if (!catchBlocks.containsKey(stmt)) {
			LinkedList<Trap> traps = new LinkedList<Trap>();
			catchBlocks.put(stmt, traps);
			procedureTraps.add(t);
		}
		catchBlocks.get(stmt).add(t);
	}


	public void addUncaughtException(BoogieType t) {
		Expression exv = this.boogieProcedure.getExceptionalReturnVariable(t);
		if (null == exv) {
			this.boogieProcedure.addExceptionalReturnVariable(t, BoogieVariableFactory
					.v().getFreshLocalVariable("$Exep", t));
			AssignStatement initvar = BoogieHelpers.createAssignment(
					this.boogieProcedure.getExceptionalReturnVariable(t),
					BoogieHelpers.getNullVariable());
			BasicBlock rootBlock = this.boogieProcedure.getRootBlock();
			if (rootBlock == null) {
				rootBlock = new BasicBlock(BoogieHelpers.createLocationTag(boogieProcedure));
				this.boogieProcedure.setBodyRoot(rootBlock);
			}
			rootBlock.addStatement(initvar, true);
		}
	}	
	
	public Expression findCatchVar(Stmt arg0) {
		for (Trap t : procedureTraps) {
			if (t.getHandlerUnit() == arg0) {
				return this.lookupLocalExceptionVar(t);
			} else {
				// Log.error("NOT: "+(t.getHandlerUnit()).toString());
			}
		}
		return null;
	}

	public Expression lookupLocalExceptionVar(Trap t) {

		if (!caughtExceptionVars.containsKey(t)) {
			BoogieType type = BoogieTypeFactory.lookupBoogieType(t
					.getException().getType());
			caughtExceptionVars.put(t, BoogieVariableFactory.v()
					.getFreshLocalVariable("$caughtEx", type));
			AssignStatement initvar = BoogieHelpers.createAssignment(
					caughtExceptionVars.get(t), BoogieHelpers.getNullVariable());
			BasicBlock rootBlock = this.boogieProcedure.getRootBlock();
			if (rootBlock == null) {
				rootBlock = new BasicBlock(BoogieHelpers.createLocationTag(boogieProcedure));
			}
			rootBlock.addStatement(initvar, true);
		}
		return caughtExceptionVars.get(t);
	}

	public Expression lookupInvokeExceptionVar(BoogieType t) {

		if (!invokeExceptionVars.containsKey(t)) {
			invokeExceptionVars.put(t, BoogieVariableFactory.v()
					.getFreshLocalVariable("$caughtEx", t));
			AssignStatement initvar = BoogieHelpers.createAssignment(
					invokeExceptionVars.get(t), BoogieHelpers.getNullVariable());
			BasicBlock rootBlock = this.boogieProcedure.getRootBlock();
			if (rootBlock == null) {
				rootBlock = new BasicBlock(BoogieHelpers.createLocationTag(boogieProcedure));
			}
			rootBlock.addStatement(initvar, true);
		}
		return invokeExceptionVars.get(t);
	}

	//TODO: this must not be a set because
	//the order is important when generating the variables
	//for a procedure call.
	public Set<BoogieType> getUncaughtExceptionTypes() {
		return this.boogieProcedure.getUncaughtTypes();
	}
	
	public void addExceptionBlock(BasicBlock catchBlock) {
		this.exceptionBlocks .add(catchBlock);
	}
	/**
	 * @return the exceptionBlocks
	 */
	public Set<BasicBlock> getExceptionBlocks() {
		return exceptionBlocks;
	}
	
}
