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

package org.joogie.ssa;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.Stack;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.QuantifiedExpression;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssertStatement;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.AssumeStatement;
import org.joogie.boogie.statements.HavocStatement;
import org.joogie.boogie.statements.InvokeStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class SSA {

	/**
	 * Boogie procedure
	 */
	private BoogieProcedure proc;

	/**
	 * C-tor
	 * 
	 * @param proc
	 *            Boogie procedure
	 */
	public SSA(BoogieProcedure proc) {
		this.proc = proc;
	}

	public void doSSA() {
		//BoogieProcedure2Dot.toDotFile(proc,"d:/"+proc.getName()+"_0.dot");

		boolean unifedExitCreated = false;

		LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
		HashSet<BasicBlock> done = new HashSet<BasicBlock>();

		HashSet<BasicBlock> exitblocks = new HashSet<BasicBlock>();

		HashMap<BasicBlock, HashMap<Variable, Integer>> blockIncarnationMap = new HashMap<BasicBlock, HashMap<Variable, Integer>>();

		todo.add(proc.getRootBlock());

		while (todo.size() > 0) {
			BasicBlock current = todo.removeFirst();
			boolean allSuccDone = true;
			for (BasicBlock pre : current.Predecessors) {
				if (!done.contains(pre)) {
					allSuccDone = false;
					break;
				}
			}

			if (!allSuccDone) {
				todo.addLast(current);
				continue;
			}

			HashMap<Variable, Integer> maxIncarnation = new HashMap<Variable, Integer>();
			for (BasicBlock pre : current.Predecessors) {
				HashMap<Variable, Integer> preIncarnation = blockIncarnationMap
						.get(pre);
				for (Entry<Variable, Integer> entry : preIncarnation.entrySet()) {
					if (maxIncarnation.containsKey(entry.getKey())) {
						Integer max = (entry.getValue() < maxIncarnation
								.get(entry.getKey())) ? maxIncarnation
								.get(entry.getKey()) : entry.getValue();
						maxIncarnation.put(entry.getKey(), max);
					} else {
						maxIncarnation.put(entry.getKey(), entry.getValue());
					}
				}
			}
			LinkedList<BasicBlock> _tmp = new LinkedList<BasicBlock>(
					current.Predecessors);
			for (BasicBlock pre : _tmp) {
				HashMap<Variable, Integer> preIncarnation = blockIncarnationMap
						.get(pre);
				Stack<Variable> diffincarnation = new Stack<Variable>();
				for (Entry<Variable, Integer> entry : preIncarnation.entrySet()) {
					if (entry.getValue() < maxIncarnation.get(entry.getKey())) {
						diffincarnation.add(entry.getKey());
					}
				}
				if (diffincarnation.size() == 0)
					continue;
				pre.disconnectFromSuccessor(current);
				BasicBlock between = new BasicBlock(pre.getLocationTag());
				pre.connectToSuccessor(between);
				between.connectToSuccessor(current);
				done.add(between);
				createFrameStatements(between, diffincarnation, maxIncarnation,
						blockIncarnationMap.get(pre),
						proc.getVarIncarnationMap());
			}

			blockSSA(current, maxIncarnation, proc.getVarIncarnationMap());
			blockIncarnationMap.put(current, maxIncarnation);

			done.add(current);
			for (BasicBlock suc : current.Successors) {
				if (!todo.contains(suc) && !done.contains(suc)) {
					todo.addFirst(suc);
				}
			}

			if (current.Successors.size() == 0) {
				exitblocks.add(current);
			}

			// if all blocks have been visited we create a unified exit block
			// to guarantee that the value of the very last incarnation of each
			// variable is correct.
			if (todo.size() == 0 && !unifedExitCreated) {
				unifedExitCreated = true;
				BasicBlock unifiedExit = new BasicBlock();
				for (BasicBlock pre : exitblocks) {
					pre.connectToSuccessor(unifiedExit);
					if (unifiedExit.getLocationTag()==null && pre.getLocationTag()!=null) {
						unifiedExit.setLocationTag(pre.getLocationTag());
					}
				}
				todo.add(unifiedExit);
				proc.setExitBlock(unifiedExit);
			}

		}
		// BoogieProcedure2Dot.toDotFile(proc,"d:/"+proc.getName()+"_A.dot");
		collabseBlocks(proc.getRootBlock()); // remove all blocks that we don't
												// need
		// BoogieProcedure2Dot.toDotFile(proc,"d:/"+proc.getName()+"_B.dot");

	}

	private void createFrameStatements(BasicBlock b, Collection<Variable> vars,
			HashMap<Variable, Integer> newvals,
			HashMap<Variable, Integer> oldvals,
			HashMap<Variable, LinkedList<Variable>> var2incarnationMap) {
		for (Variable v : vars) {
			Expression lhs = var2incarnationMap.get(v).get(newvals.get(v));
			Expression rhs = var2incarnationMap.get(v).get(oldvals.get(v));
			AssignStatement s = new AssignStatement(lhs, rhs);
			b.addStatement(s);
		}
	}

	private void blockSSA(BasicBlock b,
			HashMap<Variable, Integer> incarnationMap,
			HashMap<Variable, LinkedList<Variable>> var2incarnationMap) {
		LinkedList<Statement> statements = new LinkedList<Statement>();
		for (Statement s : b.getStatements()) {
			if (s instanceof AssignStatement) {
				Expression rhs = expressionSSA(
						((AssignStatement) s).getRight(), false,
						incarnationMap, var2incarnationMap);
				Expression lhs = expressionSSA(((AssignStatement) s).getLeft(),
						true, incarnationMap, var2incarnationMap);
				statements.add(new AssignStatement(lhs, rhs));
			} else if (s instanceof InvokeStatement) {
				// TODO this is a hack which abstracts the procedure call by
				// using a havoc statement ...
				// we should remove procedure calls earlier
				InvokeStatement ivk = (InvokeStatement) s;
				if (ivk.getInvokedProcedure().isPure()) {
					// built-in functions are preserved during SSA as they are
					// pure
					// and only used to describe basic arithmetic operations,
					// etc.
					LinkedList<Expression> args = new LinkedList<Expression>();
					for (Expression e : ivk.getArguments()) {
						args.add(expressionSSA(e, false, incarnationMap,
								var2incarnationMap));
					}
					LinkedList<Expression> rettarg = new LinkedList<Expression>();
					for (Expression e : ivk.getReturnTargets()) {
						rettarg.add(expressionSSA(e, true, incarnationMap,
								var2incarnationMap));
					}
					statements.add(new InvokeStatement(new InvokeExpression(ivk
							.getInvokedProcedure(), args), rettarg));
				} else {
					for (Expression e : ivk.getReturnTargets()) {
						expressionSSA(e, true, incarnationMap,
								var2incarnationMap);
					}
				}
				HashSet<Variable> mod = new HashSet<Variable>(
						ivk.getModifiedVars());
				for (Variable v : mod) {
					increaseIncarnation(v, incarnationMap);
					getOrCreateIncarnationVar(v, incarnationMap.get(v),
							incarnationMap, var2incarnationMap);
				}
			} else if (s instanceof HavocStatement) {
				for (Variable v : ((HavocStatement) s).getHavocVars()) {
					increaseIncarnation(v, incarnationMap);
					getOrCreateIncarnationVar(v, incarnationMap.get(v),
							incarnationMap, var2incarnationMap);
				}
			} else if (s instanceof AssertStatement) {
				Expression exp = expressionSSA(
						((AssertStatement) s).getExpression(), false,
						incarnationMap, var2incarnationMap);
				statements.add(new AssertStatement(exp));
			} else if (s instanceof AssumeStatement) {
				Expression exp = expressionSSA(
						((AssumeStatement) s).getExpression(), false,
						incarnationMap, var2incarnationMap);
				statements.add(new AssumeStatement(exp));
			}
		}
		b.setStatements(statements);
	}

	public void increaseIncarnation(Variable v,
			HashMap<Variable, Integer> incarnationMap) {
		if (!incarnationMap.containsKey(v)) {
			incarnationMap.put(v, 0);
		} else {
			incarnationMap.put(v, incarnationMap.get(v) + 1);
		}
	}

	private Expression expressionSSA(Expression e, boolean increase,
			HashMap<Variable, Integer> incarnationMap,
			HashMap<Variable, LinkedList<Variable>> var2incarnationMap) {
		if (e instanceof Variable) {
			Variable v = (Variable) e;
			if (v.isBound)
				return v; // TODO: we have to test if this causes problems ...
							// but it should work
			if (increase) {
				increaseIncarnation(v, incarnationMap);
			} else {
				if (!incarnationMap.containsKey(v)) {
					incarnationMap.put(v, 0);
				}
			}
			return getOrCreateIncarnationVar(v, incarnationMap.get(v),
					incarnationMap, var2incarnationMap);
		} else if (e instanceof ArrayReadExpression) {
			Expression idx = expressionSSA(
					((ArrayReadExpression) e).getIndexExpression(), false,
					incarnationMap, var2incarnationMap);
			Expression base = expressionSSA(
					((ArrayReadExpression) e).getBaseExpression(), increase,
					incarnationMap, var2incarnationMap);
			return new ArrayReadExpression(base, idx);
		} else if (e instanceof InvokeExpression) {
			// InvokeExpressions only occur as bulit-in procs in Assert/Assume,
			// all others are treated by blockSSA
			InvokeExpression ivk = (InvokeExpression) e;
			if (ivk.getInvokedProcedure().isPure()) {
				LinkedList<Expression> args = new LinkedList<Expression>();
				for (Expression e2 : ivk.getArguments()) {
					args.add(expressionSSA(e2, false, incarnationMap,
							var2incarnationMap));
				}
				return new InvokeExpression(ivk.getInvokedProcedure(), args);
			} else {
				Log.error("BUG! This should not be reachable");
				System.exit(-1);
			}
		} else if (e instanceof SimpleHeapAccess) {
			SimpleHeapAccess sha = (SimpleHeapAccess) e;
			Expression base = expressionSSA(sha.getBaseExpression(), false,
					incarnationMap, var2incarnationMap);
			Expression field = expressionSSA(sha.getFieldExpression(), false,
					incarnationMap, var2incarnationMap);
			Expression heap = expressionSSA(
					BoogieProgram.v().heapVariable, increase,
					incarnationMap, var2incarnationMap);
			return new SimpleHeapAccess((Variable) heap, base, field);
		} else if (e instanceof QuantifiedExpression) {
			// TODO: not tested
			QuantifiedExpression exp = (QuantifiedExpression) e;
			LinkedList<Variable> bvars = new LinkedList<Variable>();
			for (Variable v : exp.getBoundVariables()) {
				bvars.add(v.clone());
			}
			Expression term = expressionSSA(exp.getExpression(), false,
					incarnationMap, var2incarnationMap);
			return new QuantifiedExpression(exp.getQuantifier(), bvars, term);
		} else if (e instanceof BinOpExpression) {
			BinOpExpression exp = (BinOpExpression) e;
			Expression lhs = expressionSSA(exp.getLhs(), false, incarnationMap,
					var2incarnationMap);
			Expression rhs = expressionSSA(exp.getRhs(), false, incarnationMap,
					var2incarnationMap);
			return new BinOpExpression(exp.getOp(), lhs, rhs);
		} else if (e instanceof IteExpression) {
			// TODO: not tested
			IteExpression exp = (IteExpression) e;
			Expression c = expressionSSA(exp.getCond(), false, incarnationMap,
					var2incarnationMap);
			Expression th = expressionSSA(exp.getThen(), false, incarnationMap,
					var2incarnationMap);
			Expression el = expressionSSA(exp.getElse(), false, incarnationMap,
					var2incarnationMap);
			return new IteExpression(c, th, el);
		} else { // tyepexpression or constants.
			return e.clone();
		}

		return e;
	}

	private Variable getOrCreateIncarnationVar(Variable v, Integer inc,
			HashMap<Variable, Integer> incarnationMap,
			HashMap<Variable, LinkedList<Variable>> var2incarnationMap) {
		if (!var2incarnationMap.containsKey(v)
				|| var2incarnationMap.get(v) == null) {
			var2incarnationMap.put(v, new LinkedList<Variable>());
		}

		if (!incarnationMap.containsKey(v)) {
			int startIncarnation = 0;
			if (v == BoogieProgram.v().heapVariable
					|| v.getType() == BoogieBaseTypes.getIntArrType()
					|| v.getType() == BoogieBaseTypes.getRealArrType()
					|| v.getType() == BoogieBaseTypes.getRefArrType()) {
				/*
				 * this is necessary because a write-access to array or heap in
				 * smt-lib format will also refer to the previous incarnation.
				 * I.e., we have to start from 1 rather then from 0
				 */
				startIncarnation = 1;
			}
			incarnationMap.put(v, startIncarnation);
		}

		if (var2incarnationMap.get(v).size() <= incarnationMap.get(v)) {
			for (int i = var2incarnationMap.get(v).size(); i < incarnationMap
					.get(v) + 1; i++) {
				var2incarnationMap.get(v).add(createIncarnationVariable(v, i));
			}
		}
		return var2incarnationMap.get(v).get(incarnationMap.get(v));
	}

	private Variable createIncarnationVariable(Variable v, Integer inc) {
		return new SSAVariable(v, inc);
	}

	/**
	 * iterates through the program any for any two connected block that have
	 * only one successor resp. predecessor, merges them into one block. this is
	 * done to eliminate unnecessary block variables in the vc
	 * 
	 * @param b
	 */
	private void collabseBlocks(BasicBlock root) {
		LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
		LinkedList<BasicBlock> done = new LinkedList<BasicBlock>();

		todo.add(root);

		while (!todo.isEmpty()) {
			// Log.error(("TODO: ");
			// for (BasicBlock c : todo) Log.error((c.getName()+",");
			// Log.error(("");

			BasicBlock b = todo.removeFirst();
			if (b.Successors.size() == 1) {
				BasicBlock other = (b.Successors.toArray(new BasicBlock[1]))[0];
				if (other.Predecessors.size() == 1) {
					for (Statement s : other.getStatements()) {
						b.addStatement(s);
					}
					b.disconnectFromSuccessor(other);
					HashSet<BasicBlock> tmp_succ = new HashSet<BasicBlock>(
							other.Successors);
					for (BasicBlock other_succ : tmp_succ) {
						other.disconnectFromSuccessor(other_succ);
						b.connectToSuccessor(other_succ);
					}
					// if we just merged the exit block, update this in proc
					if (other == proc.getExitBlock()) {
						proc.setExitBlock(b);
					}
					todo.addFirst(b);
					continue;
				}
			}
			done.add(b);
			for (BasicBlock next : b.Successors) {
				if (!done.contains(next) && !todo.contains(next)) {
					todo.add(next);
				}
			}
		}

	}

}
