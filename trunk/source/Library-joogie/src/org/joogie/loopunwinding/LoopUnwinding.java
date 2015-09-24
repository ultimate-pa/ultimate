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

package org.joogie.loopunwinding;

import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.statements.HavocStatement;
import org.joogie.boogie.statements.InvokeStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.util.Log;

/**
 * Does the abstract loop unwinding as explained in the FMSD journal article
 * "Doomed Program Points"
 * 
 * Note that, if we actually do the abstract loop unwinding, we need a mechanism
 * to inform the reporting system that infeasible code in the first and last
 * unwinding must not be reported.
 * 
 * @author schaef
 */
public class LoopUnwinding extends AbstractLoopUnwinding {

	/**
	 * C-tor
	 * 
	 * @param proc
	 *            Boogie procedure
	 */
	public LoopUnwinding(BoogieProcedure proc) {
		super(proc);
	}

	public void unwind() {
		// TODO: maybe, instead of modifying the body, we should create a
		// loop-free clone, so we can reuse the procedure later
		// if (proc.getName().contains("removeTag")) {
		// BoogieProcedure2Dot.toDotFile(proc, "d:/0.dot");
		// }
		BasicBlock root = proc.getRootBlock();
		LoopDetection detection = new LoopDetection();
		List<LoopInfo> loops = detection.computeLoops(root);

		boolean unwindeNestedLoops = false; // TODO: this variable is only here
											// for experimental purpose and can
											// be removed later

		for (LoopInfo loop : loops) {
			Log.debug(loop);
			unwindeLoop(loop, null, unwindeNestedLoops, "");
		}

	}

	private void unwindeLoop(LoopInfo l, LoopInfo parent, boolean descend,
			String prefix) {
		if (descend) {

			LoopInfo firstIteration = new LoopInfo(prefix + "FI_", l);
			LoopInfo abstractIteration = new LoopInfo(prefix + "XX_", l);
			LoopInfo lastIteration = new LoopInfo(prefix + "LA_", l);
			LoopInfo finalIteration = new LoopInfo(prefix + "EX_", l);

			if (l.nestedLoops.size() > 0) {
				for (LoopInfo nestedloop : firstIteration.nestedLoops)
					unwindeLoop(nestedloop, firstIteration, false, prefix
							+ "FI_");
				for (LoopInfo nestedloop : abstractIteration.nestedLoops)
					unwindeLoop(nestedloop, abstractIteration, descend, prefix
							+ "XX_");
				for (LoopInfo nestedloop : lastIteration.nestedLoops)
					unwindeLoop(nestedloop, lastIteration, false, prefix
							+ "LA_");
				for (LoopInfo nestedloop : finalIteration.nestedLoops)
					unwindeLoop(nestedloop, finalIteration, false, prefix
							+ "EX_");

				// TODO: recompute the looping preds and loophead if they have
				// been modified by unwinding the nested loops
				recomputeLoopingPredecessors(firstIteration);
				recomputeLoopingPredecessors(abstractIteration);
				recomputeLoopingPredecessors(lastIteration);
				recomputeLoopingPredecessors(finalIteration);

			}

			computeHavocStatement(abstractIteration);

			for (BasicBlock b : l.loopEntries) {
				b.disconnectFromSuccessor(finalIteration.loopHead);
				b.disconnectFromSuccessor(lastIteration.loopHead);
				b.disconnectFromSuccessor(abstractIteration.loopHead);
				b.disconnectFromSuccessor(l.loopHead);
				b.connectToSuccessor(firstIteration.loopHead);
			}
			for (BasicBlock le : l.loopExit) {
				// copy is needed because we are not allowed to delete while
				// iterating
				HashSet<BasicBlock> tmp = new HashSet<BasicBlock>(
						le.Predecessors);
				for (BasicBlock b : tmp) {
					if (l.loopBody.contains(b)) {
						b.disconnectFromSuccessor(le);
					}
				}
			}

			// redirectBackEdges(firstIteration, lastIteration.loopHead);

			redirectBackEdges(firstIteration, abstractIteration.loopHead);
			redirectBackEdges(abstractIteration, lastIteration.loopHead);
			redirectBackEdges(lastIteration, finalIteration.loopHead);
			removeLoopingPaths(finalIteration);

			if (parent != null) {
				parent.loopBody.addAll(firstIteration.loopBody);
				parent.loopBody.addAll(abstractIteration.loopBody);
				parent.loopBody.addAll(lastIteration.loopBody);
				parent.loopBody.addAll(finalIteration.loopBody);
				parent.loopBody.removeAll(l.loopBody);
			}

		} else {
			LoopInfo abstractIteration = new LoopInfo(prefix + "AB_", l);
			for (LoopInfo nestedloop : abstractIteration.nestedLoops)
				unwindeLoop(nestedloop, abstractIteration, false, prefix
						+ "BC_");
			computeHavocStatement(abstractIteration);
			removeLoopingPaths(abstractIteration);
			for (BasicBlock b : l.loopEntries) {
				b.connectToSuccessor(abstractIteration.loopHead);
				b.disconnectFromSuccessor(l.loopHead);
			}
			for (BasicBlock le : l.loopExit) {
				// copy is needed because we are not allowed to delete while
				// iterating
				HashSet<BasicBlock> tmp = new HashSet<BasicBlock>(
						le.Predecessors);
				for (BasicBlock b : tmp) {
					if (l.loopBody.contains(b)) {
						b.disconnectFromSuccessor(le);
					}
				}
			}

			if (parent != null) {
				parent.loopBody.addAll(abstractIteration.loopBody);
				parent.loopBody.removeAll(l.loopBody);
			}

		}
	}

	// private void printLoopPredecessors(LoopInfo l) {
	// HashSet<BasicBlock> tmp = new HashSet<BasicBlock>();
	// tmp.add(l.loopHead);
	// for (BasicBlock b : l.loopEntries) {
	// for (BasicBlock pre : b.Predecessors) {
	// // if (l.loopBody.contains(pre))
	// tmp.add(pre);
	// }
	// }
	// for (BasicBlock b : tmp) {
	// Log.error(b.getName() + ", ");
	// }
	// }

	private void recomputeLoopingPredecessors(LoopInfo l) {
		for (BasicBlock b : l.loopHead.Predecessors) {
			if (!l.loopEntries.contains(b)) {
				l.loopingPred.add(b);
			}
		}
	}

	private void removeLoopingPaths(LoopInfo l) {
		// first check, if it is a while-do loop, then we can simply redirect
		// the backedge to a non-looping successor of the loopHead
		HashSet<BasicBlock> headexits = new HashSet<BasicBlock>();
		for (BasicBlock b : l.loopHead.Successors) {
			if (l.loopExit.contains(b))
				headexits.add(b);
		}
		if (headexits.size() > 0) {
			for (BasicBlock lp : l.loopingPred) {
				lp.disconnectFromSuccessor(l.loopHead);
				for (BasicBlock he : headexits) {
					lp.connectToSuccessor(he);
				}
			}

			return;
		} else {
			// if we have a do-while loop (i.e., the loopHead has no loop exit)
			// we prune all blocks that cannot leave the loop.
			Stack<BasicBlock> todo = new Stack<BasicBlock>();
			HashSet<BasicBlock> done = new HashSet<BasicBlock>();
			for (BasicBlock le : l.loopExit) {
				for (BasicBlock b : le.Predecessors) {
					if (l.loopBody.contains(b))
						todo.push(b);
				}
			}
			while (!todo.empty()) {
				BasicBlock current = todo.pop();
				done.add(current);
				for (BasicBlock b : current.Predecessors) {
					if (!l.loopingPred.contains(b)
							&& !l.loopEntries.contains(b)) {
						if (!todo.contains(b) && !done.contains(b))
							todo.push(b);
					}
				}
			}
			// now we prune all blocks that are not in done
			// (these are the ones that only occur on looping executions)
			HashSet<BasicBlock> prunedBlocks = new HashSet<BasicBlock>();
			for (BasicBlock b : l.loopBody) {
				if (!done.contains(b)) {
					prunedBlocks.add(b);
					HashSet<BasicBlock> tmp = new HashSet<BasicBlock>(
							b.Successors);
					for (BasicBlock b_ : tmp) {
						b.disconnectFromSuccessor(b_);
					}
					tmp = new HashSet<BasicBlock>(b.Predecessors);
					for (BasicBlock b_ : tmp) {
						b_.disconnectFromSuccessor(b);
					}
				}
			}
			l.loopBody.removeAll(prunedBlocks);
			l.loopingPred.clear();
		}
	}

	private void redirectBackEdges(LoopInfo l, BasicBlock target) {
		for (BasicBlock b : l.loopingPred) {
			b.disconnectFromSuccessor(l.loopHead);
			b.connectToSuccessor(target);
		}
	}

	private void computeHavocStatement(LoopInfo l) {
		HashSet<Variable> havocedVars = new HashSet<Variable>();
		for (BasicBlock b : l.loopBody) {
			for (Statement s : b.getStatements()) {
				if (s instanceof AssignStatement) {
					AssignStatement ass = (AssignStatement) s;
					Expression e = ass.getLeft();
					Variable v = expToVariable(e);
					if (v != null)
						havocedVars.add(v);
				} else if (s instanceof InvokeStatement) {
					InvokeStatement ivk = (InvokeStatement) s;
					List<Expression> elist = ivk.getReturnTargets();
					for (Expression e : elist) {
						Variable v = expToVariable(e);
						if (v != null)
							havocedVars.add(v);
					}
				}
			}
		}
		HavocStatement hcmd = new HavocStatement(havocedVars);
		l.loopHead.getStatements().addFirst(hcmd);

		for (BasicBlock b : l.loopExit) {
			for (BasicBlock b_ : b.Predecessors) {
				if (l.loopBody.contains(b_)) {
					b_.getStatements().addLast(hcmd.clone());
				}
			}
		}

	}

	private Variable expToVariable(Expression e) {
		if (e instanceof Variable) {
			return (Variable) e;
		} else if (e instanceof SimpleHeapAccess) {
			// SimpleHeapAccess sha = (SimpleHeapAccess)e;
			// TODO: instead of havoc'ing the whole Heap, we might have
			// something more precise
			return BoogieProgram.v().heapVariable;
		} else if (e instanceof ArrayReadExpression) {
			ArrayReadExpression are = (ArrayReadExpression) e;
			// TODO: instead of havoc'ing the whole array, we might have
			// something more precise
			return expToVariable(are.getBaseExpression());
		}
		return null;
	}

}
