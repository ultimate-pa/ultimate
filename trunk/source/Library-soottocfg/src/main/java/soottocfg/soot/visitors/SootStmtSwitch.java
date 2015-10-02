/*
 * jimple2boogie - Translates Jimple (or Java) Programs to Boogie
 * Copyright (C) 2013 Martin Schaef and Stephan Arlt
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

package soottocfg.soot.visitors;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import soot.Body;
import soot.Immediate;
import soot.PatchingChain;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BreakpointStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.NopStmt;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StmtSwitch;
import soot.jimple.TableSwitchStmt;
import soot.jimple.ThrowStmt;
import soot.jimple.toolkits.annotation.nullcheck.NullnessAnalysis;
import soot.jimple.toolkits.pointer.LocalMayAliasAnalysis;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soottocfg.cfg.Program;
import soottocfg.cfg.Variable;
import soottocfg.cfg.expression.BinaryExpression;
import soottocfg.cfg.expression.BooleanLiteral;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.InstanceOfExpression;
import soottocfg.cfg.expression.IntegerLiteral;
import soottocfg.cfg.expression.UnaryExpression;
import soottocfg.cfg.expression.BinaryExpression.BinaryOperator;
import soottocfg.cfg.expression.UnaryExpression.UnaryOperator;
import soottocfg.cfg.method.CfgBlock;
import soottocfg.cfg.method.Method;
import soottocfg.cfg.statement.AssertStatement;
import soottocfg.cfg.statement.AssignStatement;
import soottocfg.cfg.statement.CallStatement;
import soottocfg.cfg.statement.Statement;
import soottocfg.soot.SootPreprocessing;
import soottocfg.soot.invoke_resolver.InvokeResolver;
import soottocfg.soot.invoke_resolver.SimpleInvokeResolver;
import soottocfg.soot.util.MethodInfo;
import soottocfg.soot.util.SootTranslationHelpers;

/**
 * @author schaef
 */
public class SootStmtSwitch implements StmtSwitch {

	private final SootMethod sootMethod;
	private final Body sootBody;

	private final MethodInfo methodInfo;
	private final SootValueSwitch valueSwitch;

	private final PatchingChain<Unit> units;

	private CfgBlock currentBlock, entryBlock, exitBlock;
	private boolean insideMonitor = false;

	private Stmt currentStmt;
	private final Program program;

	private final LocalMayAliasAnalysis localMayAlias;
	private final NullnessAnalysis localNullness;

	public SootStmtSwitch(Body body, MethodInfo mi) {
		this.methodInfo = mi;
		this.sootBody = body;
		this.sootMethod = sootBody.getMethod();

		UnitGraph unitGraph = new CompleteUnitGraph(sootBody);
		localNullness = new NullnessAnalysis(unitGraph);
		localMayAlias = new LocalMayAliasAnalysis(unitGraph);

		this.program = SootTranslationHelpers.v().getProgram();

		this.valueSwitch = new SootValueSwitch(this);

		units = body.getUnits();
		Unit head = units.getFirst();
		// check if the block is empty.
		if (head != null) {
			this.entryBlock = methodInfo.lookupCfgBlock(head);
			this.currentBlock = this.entryBlock;
			Iterator<Unit> iterator = units.iterator();
			while (iterator.hasNext()) {
				Unit u = iterator.next();
				u.apply(this);
			}
		} else {
			this.entryBlock = new CfgBlock();
			this.currentBlock = this.entryBlock;
		}

		if (this.currentBlock != null) {
			this.exitBlock = this.currentBlock;
		} else {
			this.exitBlock = null;
		}
		// TODO: connect stuff to exit.
	}

	/**
	 * Get the set of possible aliases for the value v in the current body. This
	 * uses Soots LocalMayAliasAnalysis.
	 * 
	 * @param v
	 * @return
	 */
	public Set<Value> getMayAliasInCurrentUnit(Value v) {
		return this.localMayAlias.mayAliases(v, this.currentStmt);
	}

	public boolean mustBeNull(Unit u, Immediate i) {
		return this.localNullness.isAlwaysNullBefore(u, i);
	}

	public boolean mustBeNonNull(Unit u, Immediate i) {
		return this.localNullness.isAlwaysNonNullBefore(u, i);
	}

	public CfgBlock getEntryBlock() {
		return this.entryBlock;
	}

	public CfgBlock getExitBlock() {
		return this.exitBlock;
	}

	public MethodInfo getMethodInto() {
		return this.methodInfo;
	}

	public SootMethod getMethod() {
		return this.sootMethod;
	}

	public Stmt getCurrentStmt() {
		return this.currentStmt;
	}

	/**
	 * Checks if the current statement is synchronized or inside a monitor
	 * 
	 * @return True if the current statement is inside a monitor or synchronized
	 *         and false, otherwise.
	 */
	public boolean isSynchronizedOrInsideMonitor() {
		return this.insideMonitor || this.sootMethod.isSynchronized();
	}

	public void push(Statement stmt) {
		this.currentBlock.addStatement(stmt);
	}

	private void precheck(Stmt st) {
		this.currentStmt = st;
		// first check if we already created a block
		// for this statement.
		if (methodInfo.findBlock(st) != null) {
			// TODO: connect to predecessor.
			currentBlock = methodInfo.findBlock(st);
		}
		// If not, and we currently don't have a block,
		// create a new one.
		if (currentBlock == null) {
			currentBlock = methodInfo.lookupCfgBlock(st);
		}
	}

	@Override
	public void caseAssignStmt(AssignStmt arg0) {
		precheck(arg0);
		if (arg0.containsInvokeExpr()) {
			assert(arg0.getRightOp() instanceof InvokeExpr);
			translateMethodInvokation(arg0, arg0.getLeftOp(), arg0.getInvokeExpr());
		} else {
			translateDefinitionStmt(arg0);
		}
	}

	@Override
	public void caseBreakpointStmt(BreakpointStmt arg0) {
		precheck(arg0);
	}

	@Override
	public void caseEnterMonitorStmt(EnterMonitorStmt arg0) {
		precheck(arg0);
		arg0.getOp().apply(this.valueSwitch);
		this.valueSwitch.popExpression();
		this.insideMonitor = true;
		// TODO Havoc stuff
	}

	@Override
	public void caseExitMonitorStmt(ExitMonitorStmt arg0) {
		precheck(arg0);
		arg0.getOp().apply(this.valueSwitch);
		this.valueSwitch.popExpression();
		this.insideMonitor = false;
		// TODO:
	}

	@Override
	public void caseGotoStmt(GotoStmt arg0) {
		precheck(arg0);
		CfgBlock target = this.methodInfo.lookupCfgBlock(arg0.getTarget());
		this.currentBlock.addSuccessor(target);
		this.currentBlock = null;
	}

	@Override
	public void caseIdentityStmt(IdentityStmt arg0) {
		precheck(arg0);
		if (arg0.containsInvokeExpr()) {
			assert(arg0.getRightOp() instanceof InvokeExpr);
			translateMethodInvokation(arg0, arg0.getLeftOp(), arg0.getInvokeExpr());
		} else {
			translateDefinitionStmt(arg0);
		}
	}

	@Override
	public void caseIfStmt(IfStmt arg0) {
		precheck(arg0);
		arg0.getCondition().apply(valueSwitch);
		Expression cond = valueSwitch.popExpression();
		CfgBlock thenBlock = methodInfo.lookupCfgBlock(arg0.getTarget());
		this.currentBlock.addConditionalSuccessor(cond, thenBlock);

		/*
		 * In jimple, conditionals are of the form if (x) goto y; So we end the
		 * current block and create two new blocks for then and else branch. The
		 * new currenBlock becomes the else branch.
		 */
		Unit next = units.getSuccOf(arg0);
		if (next != null) {
			CfgBlock elseBlock = methodInfo.lookupCfgBlock(next);
			this.currentBlock.addConditionalSuccessor(new UnaryExpression(UnaryOperator.LNot, cond), elseBlock);
			this.currentBlock = elseBlock;
		} else {
			this.currentBlock.addConditionalSuccessor(new UnaryExpression(UnaryOperator.LNot, cond),
					methodInfo.getSink());
			this.currentBlock = null;
		}
	}

	@Override
	public void caseInvokeStmt(InvokeStmt arg0) {
		precheck(arg0);
		translateMethodInvokation(arg0, null, arg0.getInvokeExpr());
	}

	@Override
	public void caseLookupSwitchStmt(LookupSwitchStmt arg0) {
		precheck(arg0);

		List<Expression> cases = new LinkedList<Expression>();
		List<Unit> targets = new LinkedList<Unit>();

		arg0.getKey().apply(this.valueSwitch);
		Expression key = this.valueSwitch.popExpression();
		for (int i = 0; i < arg0.getTargetCount(); i++) {
			BinaryExpression cond = new BinaryExpression(BinaryOperator.Eq, key,
					new IntegerLiteral(arg0.getLookupValue(i)));
			cases.add(cond);
			targets.add(arg0.getTarget(i));
		}
		translateSwitch(cases, targets, arg0.getDefaultTarget());
	}

	@Override
	public void caseNopStmt(NopStmt arg0) {
		precheck(arg0);
	}

	@Override
	public void caseRetStmt(RetStmt arg0) {
		precheck(arg0);
		throw new RuntimeException("Not implemented " + arg0);
	}

	@Override
	public void caseReturnStmt(ReturnStmt arg0) {
		precheck(arg0);
		arg0.getOp().apply(valueSwitch);
		Expression returnValue = valueSwitch.popExpression();
		currentBlock.addStatement(new AssignStatement(SootTranslationHelpers.v().getSourceLocation(arg0),
				methodInfo.getReturnVariable(), returnValue));
		currentBlock.addSuccessor(methodInfo.getSink());
		currentBlock = null;
	}

	@Override
	public void caseReturnVoidStmt(ReturnVoidStmt arg0) {
		precheck(arg0);
		currentBlock.addSuccessor(methodInfo.getSink());
		currentBlock = null;
	}

	@Override
	public void caseTableSwitchStmt(TableSwitchStmt arg0) {
		precheck(arg0);
		List<Expression> cases = new LinkedList<Expression>();
		List<Unit> targets = new LinkedList<Unit>();

		arg0.getKey().apply(valueSwitch);
		Expression key = valueSwitch.popExpression();
		int counter = 0;
		for (int i = arg0.getLowIndex(); i <= arg0.getHighIndex(); i++) {
			Expression cond = new BinaryExpression(BinaryOperator.Eq, key, new IntegerLiteral(i));
			cases.add(cond);
			targets.add(arg0.getTarget(counter));
			counter++;
		}
		translateSwitch(cases, targets, arg0.getDefaultTarget());
	}

	@Override
	public void caseThrowStmt(ThrowStmt arg0) {
		precheck(arg0);
		arg0.getOp().apply(valueSwitch);
		Expression exception = valueSwitch.popExpression();
		currentBlock.addStatement(new AssignStatement(SootTranslationHelpers.v().getSourceLocation(arg0),
				methodInfo.getExceptionVariable(), exception));
		// TODO connect to the next block
	}

	@Override
	public void defaultCase(Object arg0) {
		throw new RuntimeException("Case not implemented");
	}

	/**
	 * Translates a set of switch cases into a nested IfThenElse of the form: if
	 * (case1) goto target1 else { if (case2) goto target2 else { ... Asserts
	 * that size of cases and targets is equal.
	 * 
	 * @param cases
	 * @param targets
	 * @param defaultTarget
	 */
	private void translateSwitch(List<Expression> cases, List<Unit> targets, Unit defaultTarget) {
		assert(cases.size() == targets.size());
		for (int i = 0; i < cases.size(); i++) {
			CfgBlock elseCase;
			if (i == cases.size() - 1 && defaultTarget != null) {
				elseCase = methodInfo.lookupCfgBlock(defaultTarget);
			} else {
				elseCase = new CfgBlock();
			}
			currentBlock.addConditionalSuccessor(cases.get(i), methodInfo.lookupCfgBlock(targets.get(i)));
			currentBlock.addConditionalSuccessor(new UnaryExpression(UnaryOperator.LNot, cases.get(i)), elseCase);
			currentBlock = elseCase;
		}
	}

	private void translateMethodInvokation(Unit u, Value optionalLhs, InvokeExpr call) {
		if (isHandledAsSpecialCase(u, optionalLhs, call)) {
			return;
		}
		// translate the expressions in the arguments first.
		LinkedList<Expression> args = new LinkedList<Expression>();
		for (int i = 0; i < call.getArgs().size(); i++) {
			call.getArg(i).apply(valueSwitch);
			args.add(valueSwitch.popExpression());
		}

		Expression baseExpression = null;
		// List of possible virtual methods that can be called at this point.
		// Order matters here.
		List<SootMethod> possibleTargets = new LinkedList<SootMethod>();
		if (call instanceof InstanceInvokeExpr) {
			InstanceInvokeExpr iivk = (InstanceInvokeExpr) call;
			iivk.getBase().apply(valueSwitch);
			baseExpression = valueSwitch.popExpression();
			// add the "this" variable to the list of args
			args.addFirst(baseExpression);
			// TODO: assert that base!=null

			// this include Interface-, Virtual, and SpecialInvokeExpr
			if (call.getMethod().isConstructor() && call instanceof SpecialInvokeExpr) {
				possibleTargets.add(call.getMethod());
			} else {
				// TODO: Create the InvokeResolver elsewhere.
				// InvokeResolver ivkr = new DefaultInvokeResolver();
				InvokeResolver ivkr = new SimpleInvokeResolver();
				possibleTargets.addAll(ivkr.resolveVirtualCall(this.sootBody, u, iivk));
			}
		} else if (call instanceof StaticInvokeExpr) {
			possibleTargets.add(call.getMethod());
		} else if (call instanceof DynamicInvokeExpr) {
			DynamicInvokeExpr divk = (DynamicInvokeExpr) call;
			throw new RuntimeException("Ignoring dynamic invoke: " + divk.toString());
		} else {
			throw new RuntimeException("Cannot compute instance for " + call.getClass().toString());
		}

		List<Expression> receiver = new LinkedList<Expression>();
		if (optionalLhs != null) {
			optionalLhs.apply(valueSwitch);
			receiver.add(valueSwitch.popExpression());
		}
		receiver.add(this.methodInfo.getExceptionVariable());

		if (possibleTargets.size() == 1) {
			Method method = program.loopupMethod(possibleTargets.get(0).getSignature());
			CallStatement stmt = new CallStatement(SootTranslationHelpers.v().getSourceLocation(u), method, args,
					receiver);
			this.currentBlock.addStatement(stmt);
		} else {
			assert(!possibleTargets.isEmpty());
			assert(baseExpression != null);
			CfgBlock join = new CfgBlock();
			for (SootMethod m : possibleTargets) {
				Method method = program.loopupMethod(m.getSignature());
				Variable v = SootTranslationHelpers.v().lookupTypeVariable(m.getDeclaringClass().getType());

				CfgBlock thenBlock = new CfgBlock();
				thenBlock.addStatement(
						new CallStatement(SootTranslationHelpers.v().getSourceLocation(u), method, args, receiver));
				thenBlock.addSuccessor(join);
				this.currentBlock.addConditionalSuccessor(new InstanceOfExpression(baseExpression, v), thenBlock);
				CfgBlock elseBlock = new CfgBlock();
				this.currentBlock.addConditionalSuccessor(
						new UnaryExpression(UnaryOperator.LNot, new InstanceOfExpression(baseExpression, v)),
						elseBlock);
				this.currentBlock = elseBlock;
			}
			this.currentBlock.addSuccessor(join);
			this.currentBlock = join;

			// TODO
			// for (RefType t : TrapManager.getExceptionTypesOf(u,
			// sootBlock.getBody())) {
			// System.err.println("\t type "+t);
			// }
			//
			// for (Trap t : TrapManager.getTrapsAt(u, sootBlock.getBody())) {
			// System.err.println("\t type "+t.getException());
			// }
		}
	}

	/**
	 * Check if the call is a special case such as System.exit. If so, translate
	 * it and return true. Otherwise, ignore it and return false.
	 * 
	 * @param u
	 * @param optionalLhs
	 * @param call
	 * @return true, if its a special method that is handled by the procedure,
	 *         and false, otherwise.
	 */
	private boolean isHandledAsSpecialCase(Unit u, Value optionalLhs, InvokeExpr call) {
		if (call.getMethod() == SootPreprocessing.v().getAssertMethod()) {
			assert(optionalLhs == null);
			assert(call.getArgCount() == 1);
			call.getArg(0).apply(valueSwitch);
			currentBlock.addStatement(
					new AssertStatement(SootTranslationHelpers.v().getSourceLocation(u), valueSwitch.popExpression()));
			return true;
		}
		if (call.getMethod().getSignature().contains("<java.lang.String: int length()>")) {
			assert(call instanceof InstanceInvokeExpr);
			Expression rhs = SootTranslationHelpers.v().getMemoryModel()
					.mkStringLengthExpr(((InstanceInvokeExpr) call).getBase());
			if (optionalLhs != null) {
				optionalLhs.apply(valueSwitch);
				Expression lhs = valueSwitch.popExpression();
				currentBlock
						.addStatement(new AssignStatement(SootTranslationHelpers.v().getSourceLocation(u), lhs, rhs));
			}
			return true;
		}
		if (call.getMethod().getSignature().contains("<java.lang.System: void exit(int)>")) {
			throw new RuntimeException("todo");
		}

		if (call.getMethod().getDeclaringClass().getName().contains("org.junit.Assert")) {
			// staticinvoke <org.junit.Assert: void fail()>()
			if (call.getMethod().getName().equals("fail")) {
				currentBlock.addStatement(new AssertStatement(SootTranslationHelpers.v().getSourceLocation(u),
						BooleanLiteral.falseLiteral()));
				return true;
			}
			if (call.getMethod().getName().equals("assertTrue")) {
				currentBlock.addStatement(new AssertStatement(SootTranslationHelpers.v().getSourceLocation(u),
						BooleanLiteral.falseLiteral()));
				return true;
			}
			throw new RuntimeException("we should hardcode JUnit stuff "
					+ call.getMethod().getDeclaringClass().getName() + "  method " + call.getMethod().getName());
		}

		if (call.getMethod().getDeclaringClass().getName().contains("Preconditions")) {
			throw new RuntimeException(
					"we should hardcode Guava stuff " + call.getMethod().getDeclaringClass().getName());
		}

		return false;
	}

	private void translateDefinitionStmt(DefinitionStmt def) {
		Value lhs = def.getLeftOp();
		Value rhs = def.getRightOp();
		/*
		 * Distinguish the case when the lhs is an array/instance access to
		 * ensure that we create an ArrayStoreExpression and not an assignment
		 * of two reads.
		 */
		if (lhs instanceof InstanceFieldRef || lhs instanceof ArrayRef) {
			SootTranslationHelpers.v().getMemoryModel().mkHeapAssignment(def, lhs, rhs);
		} else {
			lhs.apply(valueSwitch);
			Expression left = valueSwitch.popExpression();
			rhs.apply(valueSwitch);
			Expression right = valueSwitch.popExpression();
			currentBlock
					.addStatement(new AssignStatement(SootTranslationHelpers.v().getSourceLocation(def), left, right));
		}
	}

}
