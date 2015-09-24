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
import java.util.List;
import java.util.Map.Entry;
import java.util.Stack;

import org.joogie.boogie.BasicBlock;

/**
 * computeLoops() computes a list of LoopInfo, containing one LoopInfo for each
 * non-nested loop. All nested loop are represented as children in these
 * LoopInfo WARNING: computeLoops(root) prunes all blocks that are not reachable
 * from root.
 * 
 * @author schaef
 */
public class LoopDetection {

	public List<LoopInfo> computeLoops(BasicBlock root) {
		pruneUnreachable(root);
		HashMap<BasicBlock, HashSet<BasicBlock>> loopHeads = new HashMap<BasicBlock, HashSet<BasicBlock>>();

		LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
		HashSet<BasicBlock> done = new HashSet<BasicBlock>();
		todo.push(root);
		while (todo.size() > 0) {
			BasicBlock current = todo.removeFirst();

			boolean ready = true;
			for (BasicBlock pre : current.Predecessors) {
				if (!done.contains(pre)) {
					if (!isLoop(current, pre, todo, done,
							new HashSet<BasicBlock>())) {
						todo.addLast(current);
						ready = false;
						break;
					} else {
						current.IsLoopHead = true;
						if (!loopHeads.containsKey(current)) {
							loopHeads.put(current, new HashSet<BasicBlock>());
						}
						loopHeads.get(current).add(pre);
					}
				}
			}
			if (!ready)
				continue;

			done.add(current);

			for (BasicBlock suc : current.Successors) {
				if (!todo.contains(suc) && !done.contains(suc)) {
					todo.addFirst(suc);
				}
			}
		}
		// now that we have all loopheads and their looping predecessors, we
		// collect the loops
		HashMap<BasicBlock, LoopInfo> loopInfos = collectLoopInfo(loopHeads);

		LinkedList<LoopInfo> loops = new LinkedList<LoopInfo>();
		for (Entry<BasicBlock, LoopInfo> entry : loopInfos.entrySet()) {
			loops.add(entry.getValue());
		}
		return loops;
	}

	// private void debugprint(LoopInfo l, String indent) {
	// Log.error(indent);
	// Log.error(l.loopHead.getName());
	// for (LoopInfo nl : l.nestedLoops) {
	// debugprint(nl, indent+"\t");
	// }
	// }

	private boolean isLoop(BasicBlock loophead, BasicBlock loopNode,
			LinkedList<BasicBlock> todo, HashSet<BasicBlock> done,
			HashSet<BasicBlock> visited) {
		// Log.error("B" + visited.size() + " " + loophead.getName() +
		// "/"+loopNode.getName());
		if (loophead.getName().equals(loopNode.getName()))
			return true;
		if (todo.contains(loopNode) || done.contains(loopNode)
				|| visited.contains(loopNode))
			return false;
		visited.add(loopNode);
		for (BasicBlock pre : loopNode.Predecessors) {
			if (isLoop(loophead, pre, todo, done, visited)) {
				return true;
			}
		}
		return false;
	}

	public void pruneUnreachable(BasicBlock root) {
		Stack<BasicBlock> todo = new Stack<BasicBlock>();
		HashSet<BasicBlock> done = new HashSet<BasicBlock>();
		todo.push(root);
		// first collect all forward reachable nodes in "done"
		while (!todo.empty()) {
			BasicBlock current = todo.pop();
			done.add(current);
			for (BasicBlock suc : current.Successors) {
				if (!done.contains(suc) && !todo.contains(suc)) {
					todo.add(suc);
				}
			}
		}

		for (BasicBlock b : done) {
			HashSet<BasicBlock> newPre = new HashSet<BasicBlock>();
			for (BasicBlock pre : b.Predecessors) {
				if (done.contains(pre))
					newPre.add(pre);
			}
			b.Predecessors = newPre;
		}
	}

	/**
	 * Return a map that provides one LoopInfo for each top level loop. Nested
	 * loops are given in the LoopInfo of their surrounding loops. TODO: This
	 * implementation is not optimal but works for now. At some point we have to
	 * refactor this to make it more efficient.
	 * 
	 * @param loopHeads
	 * @return
	 */
	private HashMap<BasicBlock, LoopInfo> collectLoopInfo(
			HashMap<BasicBlock, HashSet<BasicBlock>> loopHeads) {
		HashMap<BasicBlock, LoopInfo> foundloops = new HashMap<BasicBlock, LoopInfo>();
		HashMap<BasicBlock, LoopInfo> allloops = new HashMap<BasicBlock, LoopInfo>();
		for (Entry<BasicBlock, HashSet<BasicBlock>> entry : loopHeads
				.entrySet()) {
			if (!allloops.containsKey(entry.getKey())) {
				collectLoopBody(entry.getKey(), loopHeads, foundloops, allloops);
			}
		}
		return foundloops;
	}

	/***
	 * Collect LoopInfo fields for all loops
	 * 
	 * @param loopHead
	 *            the entry block of the loop
	 * @param loopHeads
	 *            the list of all previously detected loopheads to identify
	 *            nested loops
	 * @param unnestedloops
	 *            a map that assigns a LoopInfo to each loophead that is not
	 *            nested in another loop
	 * @param allloops
	 *            a map that assigns a loopinfo to each loophead. WARNING, this
	 *            is only used to avoid iterating over nested loops in
	 *            collectLoopInfo.
	 */
	private void collectLoopBody(BasicBlock loopHead,
			HashMap<BasicBlock, HashSet<BasicBlock>> loopHeads,
			HashMap<BasicBlock, LoopInfo> unnestedloops,
			HashMap<BasicBlock, LoopInfo> allloops) {

		HashSet<BasicBlock> loopBody = new HashSet<BasicBlock>();
		HashSet<BasicBlock> tmpSuccessors = new HashSet<BasicBlock>();
		tmpSuccessors.addAll(loopHead.Successors);

		HashSet<BasicBlock> loopingPreds = loopHeads.get(loopHead);

		Stack<BasicBlock> nestedLoopHeads = new Stack<BasicBlock>();

		for (BasicBlock pre : loopingPreds) {
			Stack<BasicBlock> todo = new Stack<BasicBlock>();
			todo.push(pre);
			while (!todo.empty()) {
				BasicBlock current = todo.pop();
				loopBody.add(current);
				if (current == loopHead)
					continue; // stop when returning to the loop head
				if (loopHeads.containsKey(current)) {
					// Log.error(current.getName() +
					// " is a nested loop in " + loopHead.getName());
					// do the nested loop first
					if (!nestedLoopHeads.contains(current)) {
						collectLoopBody(current, loopHeads, unnestedloops,
								allloops);
						nestedLoopHeads.push(current);
						loopBody.addAll(unnestedloops.get(current).loopBody);
						unnestedloops.get(current).isNestedLoop = true;
					}
				}
				tmpSuccessors.addAll(current.Successors);
				for (BasicBlock prepre : current.Predecessors) {
					if (!loopBody.contains(prepre))
						todo.add(prepre);
				}
			}
		}
		tmpSuccessors.removeAll(loopBody);
		LoopInfo loop = new LoopInfo(loopHead, loopingPreds, loopBody,
				tmpSuccessors);
		// loop.nesteLoopHeads.addAll(nestedLoopHeads);

		for (BasicBlock b : nestedLoopHeads) {
			if (unnestedloops.containsKey(b)) {
				loop.nestedLoopHeads.add(b);
				loop.nestedLoops.add(unnestedloops.get(b));
				unnestedloops.remove(b);
			}

		}

		unnestedloops.put(loopHead, loop);
		allloops.put(loopHead, loop);

	}
}
