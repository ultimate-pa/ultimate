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

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Stack;

import org.joogie.boogie.BasicBlock;

/**
 * @author schaef
 */
public class LoopInfo {

	public BasicBlock loopHead = null;
	public HashSet<BasicBlock> loopingPred = null;
	public HashSet<BasicBlock> loopBody = null;
	public HashSet<BasicBlock> loopExit = null;
	public Stack<BasicBlock> nestedLoopHeads = new Stack<BasicBlock>();
	public LinkedList<LoopInfo> nestedLoops = new LinkedList<LoopInfo>();
	public HashSet<BasicBlock> loopEntries = new HashSet<BasicBlock>();

	// TODO: Hack!
	public HashMap<BasicBlock, BasicBlock> blockCloneMap = new HashMap<BasicBlock, BasicBlock>();

	public boolean isNestedLoop = false;

	public LoopInfo(BasicBlock loophead, HashSet<BasicBlock> loopingpred,
			HashSet<BasicBlock> loopbody, HashSet<BasicBlock> loopexit) {
		loopHead = loophead;
		loopingPred = loopingpred;
		loopBody = loopbody;
		loopExit = loopexit;
		for (BasicBlock b : loopHead.Predecessors) {
			if (!loopingPred.contains(b))
				loopEntries.add(b);
		}
	}

	public LoopInfo(String prefix, LoopInfo l) {
		this.loopBody = new HashSet<BasicBlock>();
		this.loopingPred = new HashSet<BasicBlock>();

		for (LoopInfo nested : l.nestedLoops) {
			LoopInfo newnested = new LoopInfo(prefix, nested);
			this.nestedLoops.add(newnested);
			this.loopBody.addAll(newnested.loopBody);
			this.blockCloneMap.putAll(newnested.blockCloneMap);
		}

		// clone all blocks in the loop body
		for (BasicBlock b : l.loopBody) {
			BasicBlock clone = null;
			if (!this.blockCloneMap.containsKey(b)) {
				clone = b.clone(prefix);
				blockCloneMap.put(b, clone);
				loopBody.add(clone);
			} else {
				clone = this.blockCloneMap.get(b);
			}
			if (b == l.loopHead) {
				this.loopHead = clone;
			}
			if (l.loopingPred.contains(b)) {
				this.loopingPred.add(clone);
			}
		}
		// fix the edges between the cloned blocks
		for (BasicBlock b : l.loopBody) {
			BasicBlock clone = blockCloneMap.get(b);
			HashSet<BasicBlock> tmp = new HashSet<BasicBlock>(b.Successors);
			for (BasicBlock b2 : tmp) {
				if (blockCloneMap.containsKey(b2)) {
					clone.disconnectFromSuccessor(b2);
					clone.connectToSuccessor(blockCloneMap.get(b2));
				} else {
					clone.connectToSuccessor(b2);
				}
			}
			tmp = new HashSet<BasicBlock>(b.Predecessors);
			for (BasicBlock b2 : tmp) {
				if (blockCloneMap.containsKey(b2)) {
					b2.disconnectFromSuccessor(clone);
					blockCloneMap.get(b2).connectToSuccessor(clone);
				} else {
					b2.connectToSuccessor(clone);
				}
			}
		}

		loopEntries.addAll(l.loopEntries);
		loopExit = new HashSet<BasicBlock>(l.loopExit);

		for (LoopInfo nested : this.nestedLoops) {
			// fix the loop entries for the nested loops
			HashSet<BasicBlock> tmp = new HashSet<BasicBlock>();
			for (BasicBlock b : nested.loopEntries) {
				if (blockCloneMap.containsKey(b)) {
					tmp.add(blockCloneMap.get(b));
					b.disconnectFromSuccessor(nested.loopHead);
					blockCloneMap.get(b).connectToSuccessor(nested.loopHead);
				} else {
					tmp.add(b);
				}
			}
			nested.loopEntries = tmp;
			// fix the loop exit for the nested loops
			tmp = new HashSet<BasicBlock>();
			for (BasicBlock b : nested.loopExit) {
				if (blockCloneMap.containsKey(b)) {
					HashSet<BasicBlock> _pre = new HashSet<BasicBlock>(
							b.Predecessors);
					for (BasicBlock b2 : _pre) {
						if (nested.loopBody.contains(b2)) {
							b2.disconnectFromSuccessor(b);
							b2.connectToSuccessor(blockCloneMap.get(b));
						}
					}
					tmp.add(blockCloneMap.get(b));
				} else {
					tmp.add(b);
				}
			}
			nested.loopExit = tmp;
		}

	}

	@Override
	public String toString() {
		return toString("");
	}

	public String toString(String prefix) {
		StringBuilder sb = new StringBuilder();
		sb.append(">> Loop: " + loopHead.toString() + "\n");
		// sb.append("loop head pre:\n");
		// for (BasicBlock b : loopHead.Predecessors) {
		// sb.append(" " + b.toString());
		// }
		// sb.append("\n");
		// sb.append(">> Body:\n");
		// sb.append(">>\t");
		// for (BasicBlock b : loopBody) {
		// sb.append(" " + b.toString());
		// }
		// sb.append("\n");
		// sb.append(">>");
		// sb.append(">> Exit:\n");
		// sb.append(">>\t");
		// for (BasicBlock b : loopExit) {
		// sb.append(" " + b.toString());
		// }
		// sb.append("\n");
		int i = 0;
		for (LoopInfo n : this.nestedLoops) {
			sb.append(">> Nested Loop " + (i++) + "\n");
			// sb.append(n.toString(prefix +"\t"));
			sb.append(n);
		}
		sb.append("\n");

		return sb.toString();
	}

}
