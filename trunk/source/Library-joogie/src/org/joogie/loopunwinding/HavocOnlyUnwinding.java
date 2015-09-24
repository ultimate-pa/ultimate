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
 * @author schaef
 */
public class HavocOnlyUnwinding extends AbstractLoopUnwinding {

	/**
	 * C-tor
	 * 
	 * @param proc
	 *            Boogie procedure
	 */
	public HavocOnlyUnwinding(BoogieProcedure proc) {
		super(proc);
		this.proc = proc;
	}

	public void unwind() {
		BasicBlock root = proc.getRootBlock();
		LoopDetection detection = new LoopDetection();
		List<LoopInfo> loops = detection.computeLoops(root);

		for (LoopInfo loop : loops) {
			Log.debug(loop);
			havocLoop(loop);
		}		
	}
	
	private void havocLoop(LoopInfo loop) {
		//havoc the nested loops first
		for (LoopInfo nest : loop.nestedLoops) {
			havocLoop(nest);
		}
		
		loop.loopHead.addStatement(computeHavocStatement(loop), true);
		
		HashSet<BasicBlock> nonloopingsuccs = new HashSet<BasicBlock>(); 
		for (BasicBlock b : loop.loopHead.Successors) {
			if (!loop.loopBody.contains(b)) {
				nonloopingsuccs.add(b);
			} 
		}
		//nonloopingsuccs.addAll(loop.loopExit);
		
		if (nonloopingsuccs.size()==0) {
			//TODO: this happens for while true....
			//I have no idea how to handle this.
			//add the runtime exception and run it on argouml to find
			//cases of this.
			//throw new RuntimeException();
		}
		
		for (BasicBlock b : loop.loopingPred) {
			b.disconnectFromSuccessor(loop.loopHead);
			b.addStatement(computeHavocStatement(loop), false);
			for (BasicBlock succ : nonloopingsuccs) {
				b.connectToSuccessor(succ);
			}
		}

		for (BasicBlock b : loop.loopExit) {
			b.addStatement(computeHavocStatement(loop), true);
		}
	}

	
	private HavocStatement computeHavocStatement(LoopInfo l) {
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
		return new HavocStatement(havocedVars);
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
