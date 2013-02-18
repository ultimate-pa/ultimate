/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.PatternCompilerUtils.InsnSequence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.AppTermNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.ConstTermNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.Edge;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.TermNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.VarNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.BindTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CompareTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.FindTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ReverseTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IntAllocator;


public class DefaultPatternCompiler implements IPatternCompiler {

	@Override
	public TriggerData compile(Set<TermVariable> vars,Term[] triggers, ConvertFormula converter) {
		InsnSequence sequence = new InsnSequence();
		Map<TermVariable,Integer> subst = new HashMap<TermVariable, Integer>();
		TermDAG dag = new TermDAG();
		TermNode[] roots = dag.buildDAG(triggers);
		CCTerm[] initregs = dag.getConstants(converter);
		IntAllocator allocator =
			new IntAllocator(initregs.length,Integer.MAX_VALUE);
		
		Map<TermNode, TermNode[]> equalityMap = new HashMap<TermNode, TermNode[]>();
		Set<TermNode> rootNodes = new HashSet<TermNode>();
		Set<TermNode> leafs = new HashSet<TermNode>();
		for(int i = 0; i < roots.length; i++) {
			assert(roots[i] instanceof AppTermNode);
			AppTermNode trigger = (AppTermNode)roots[i];
			FunctionSymbol symbol = trigger.getSymbol();			
			if(symbol.isIntern() && symbol.getName().equals("=")) {
				TermNode[] eq = new TermNode[2];
				int j = 0;
				for(Edge e : roots[i].getOutgoing()) {
					eq[j] = e.m_To;
					j++;
				}
				equalityMap.put(roots[i], eq);
				for(int ii = 0; ii < eq.length; ii++)
					if(eq[ii] instanceof AppTermNode) 
						rootNodes.add(eq[ii]);
			} else 
				rootNodes.add(roots[i]);
		}
		
		Set<TermNode> constants = new HashSet<TermNode>();
		
		for(ConstTermNode ctn : dag.getConstants()) {
			leafs.add(ctn);
			constants.add(ctn);
		}
		for(VarNode vn : dag.getVars())
			leafs.add(vn);
		
		//Map<Root, Map<Leaf, Queue<Edge>>>
		Map<TermNode, Map<TermNode, Deque<Edge>>> longestPathMap;
		longestPathMap = findLongestPaths(rootNodes, leafs);
		
		class Pair<E1, E2> {
			E1 m_Value1;
			E2 m_Value2;
			
			Pair(E1 value1, E2 value2) {
				this.m_Value1 = value1;
				this.m_Value2 = value2;
			}
		}
		
		// Begin presorting
		// Find all groups
		if(roots.length > 1) {
			Map<TermVariable, Pair<Set<TermVariable>, Queue<Integer>>> sort = new HashMap<TermVariable, Pair<Set<TermVariable>, Queue<Integer>>>();
			Map<Integer, TermVariable[]> toSubstitute = new HashMap<Integer, TermVariable[]>();
			for(int i = 0; i < roots.length; i++) {
				// get all variables and constants which can be reached from current root
				Map<TermNode, Deque<Edge>> c_traj = longestPathMap.get(roots[i]);
				Set<Pair<Set<TermVariable>, Queue<Integer>>> group = new HashSet<Pair<Set<TermVariable>, Queue<Integer>>>();
				Set<TermNode> c_leafs = (c_traj == null) ? null : c_traj.keySet();
				if(c_leafs == null) {
					TermNode[] eq = equalityMap.get(roots[i]);
					if(eq[0] instanceof VarNode && eq[1] instanceof VarNode) {
						TermVariable[] termVar = new TermVariable[2];
						termVar[0] = ((VarNode) eq[0]).getVariable();
						termVar[1] = ((VarNode) eq[1]).getVariable();
						toSubstitute.put(i, termVar);
						continue;
					} 
					else {
						c_leafs = new HashSet<TermNode>();
						for(int j = 0; j < eq.length; j++) 
							if(eq[j] instanceof VarNode)
								c_leafs.add(eq[j]);
							else if(eq[j] instanceof AppTermNode)
								for(TermNode c_n : longestPathMap.get(eq[j]).keySet())
									if(c_n instanceof VarNode)
										c_leafs.add(c_n);
					}
				}
				for(TermNode leaf : c_leafs)
					if(leaf instanceof VarNode) {
						TermVariable var = ((VarNode) leaf).getVariable();
						Pair<Set<TermVariable>, Queue<Integer>> pair = sort.get(var);
						if(pair != null) 
							group.add(pair);
					}
				if(group.size() == 0 || group.size() > 1) {
					Set<TermVariable> varSet = new HashSet<TermVariable>();
					Queue<Integer> intQueue = new ConcurrentLinkedQueue<Integer>();
					Pair<Set<TermVariable>, Queue<Integer>> pair = new Pair<Set<TermVariable>, Queue<Integer>>(varSet, intQueue);
					intQueue.add( i );
					for(TermNode leaf : c_leafs)
						if(leaf instanceof VarNode) {
							TermVariable var = ((VarNode) leaf).getVariable();
							varSet.add(var);
							sort.put(var, pair);
						}
					if(group.size() > 1) {
						for(Pair<Set<TermVariable>, Queue<Integer>> pGroup : group) {
							intQueue.addAll(pGroup.m_Value2);
							for(TermVariable var : pGroup.m_Value1)
								if(!pair.m_Value1.contains(pGroup)) {
									pair.m_Value1.add(var);
									sort.remove(var);
									sort.put(var, pair);
								}
						}
					}
				} else if(group.size() == 1) {
					Pair<Set<TermVariable>, Queue<Integer>> pair = null;
					for(Pair<Set<TermVariable>, Queue<Integer>> p : group)
						pair = p;
					for(TermNode leaf : c_leafs) 
						if(leaf instanceof VarNode) {
							TermVariable var = ((VarNode) leaf).getVariable();
							if(!pair.m_Value1.contains(var)) 
								pair.m_Value1.add(var);
						}
					pair.m_Value2.add( i );
				} 
			}
			
			while(toSubstitute.size() != 0) {
				Map<Integer, TermVariable[]> newContent = new HashMap<Integer, TermVariable[]>();
				for(int i : toSubstitute.keySet()) {
					TermVariable[] eq = toSubstitute.get(i);
					boolean foundSubstitution = false;
					Pair<Set<TermVariable>, Queue<Integer>> pair0, pair1;
					pair0 = sort.get(eq[0]);
					pair1 = sort.get(eq[1]);
					if(pair0 != null && pair1 != null) {
						foundSubstitution = true;
						if(pair0.equals(pair1))
							pair0.m_Value2.add(i);
						else {
							Set<TermVariable> varSet = new HashSet<TermVariable>();
							Queue<Integer> intQueue = new ConcurrentLinkedQueue<Integer>();
							intQueue.add(i);
							varSet.add(eq[0]);
							varSet.add(eq[1]);
							intQueue.addAll(pair0.m_Value2);
							intQueue.addAll(pair1.m_Value2);
							Pair<Set<TermVariable>, Queue<Integer>> pair = new Pair<Set<TermVariable>, Queue<Integer>>(varSet, intQueue);
							for(TermVariable v : pair0.m_Value1) {
								sort.remove(v);
								varSet.add(v);
								sort.put(v, pair);
							}
							for(TermVariable v : pair1.m_Value1) {
								sort.remove(v);
								varSet.add(v);
								sort.put(v, pair);
							}
						}
					}
					else if(pair0 != null || pair1 != null) {
						foundSubstitution = true;
						Pair<Set<TermVariable>, Queue<Integer>> pair = null;
						if(pair0 != null)
							pair = pair0;
						else if(pair1 != null)
							pair = pair1;					
						pair.m_Value1.add(eq[0]);
						pair.m_Value1.add(eq[1]);
						pair.m_Value2.add(i);
						sort.put(eq[0], pair);
						sort.put(eq[1], pair);
					}
						
					if(!foundSubstitution)
						newContent.put(i, eq);
					
				}
				if (toSubstitute.size() == newContent.size())
					break;
				
				toSubstitute = newContent;
			}
			
			if(toSubstitute.size() > 0) 
				return null;
			
			ArrayList<Queue<Integer>> sortedTrigger = new ArrayList<Queue<Integer>>();
			Set<Queue<Integer>> unsortedTrigger = new HashSet<Queue<Integer>>();
			for(Pair<Set<TermVariable>, Queue<Integer>> pair : sort.values())
				unsortedTrigger.add(pair.m_Value2);
	 
			while(!unsortedTrigger.isEmpty()) {
				Queue<Integer> first = null;
				for(Queue<Integer> set : unsortedTrigger)
					if(first == null || first.size() < set.size())
						first = set;
				unsortedTrigger.remove(first);
				sortedTrigger.add(first);
			}
			
			TermNode[] sortedRoots = new TermNode[roots.length];
			int sortedRootsIdx = 0;
			for(Queue<Integer> s : sortedTrigger)
				while(!s.isEmpty()) {
					sortedRoots[sortedRootsIdx] = roots[s.poll()];
					sortedRootsIdx++;
				}
			roots = sortedRoots;
		}
		
		// End presorting
		
		// assert(vars.containsAll(sort.keySet()));
		
		for(int i = 0; i < roots.length; i++) {
			if(rootNodes.contains(roots[i])) {
				AppTermNode app = (AppTermNode)roots[i];
				compile(converter, app, sequence, subst, allocator, longestPathMap.get(roots[i]), dag, constants);
			} else {
				TermNode[] outgoing = equalityMap.get(roots[i]);
				assert(outgoing.length == 2);
				if(( !outgoing[0].isInRegister() && !outgoing[1].isInRegister() ) 
						&& (outgoing[0] instanceof VarNode && outgoing[1] instanceof VarNode)) {
					return null;
				}
				else {
					for(int j = 0; j < 2;  j++) 
						if(!outgoing[j].isInRegister() && outgoing[j] instanceof AppTermNode) {
							AppTermNode app = (AppTermNode)outgoing[j];
							compile(converter, app, sequence, subst, allocator, longestPathMap.get(app), dag, constants);
						}
					if(!outgoing[0].isInRegister()) {
						VarNode var = (VarNode)outgoing[0];
						subst.put(var.getVariable(), outgoing[1].getRegPos());
						var.setRegPos(outgoing[1].getRegPos());
					} 
					else if(!outgoing[1].isInRegister()) {
						VarNode var = (VarNode)outgoing[1];
						subst.put(var.getVariable(), outgoing[0].getRegPos());
						var.setRegPos(outgoing[0].getRegPos());
					}
					else if(outgoing[0].getRegPos() != outgoing[1].getRegPos())
						sequence.append(new CompareTrigger(outgoing[0].getRegPos(), outgoing[1].getRegPos()));
					for(Edge edge : roots[i].getOutgoing())
						edge.mark();
				}
			}
		}
		
		// assert(vars.containsAll(subst.keySet()));
		sequence.append(new YieldTrigger(subst));
		return sequence.finish(initregs);
	}
	
	private void compile(ConvertFormula converter, AppTermNode trigger, InsnSequence sequence, 
			Map<TermVariable, Integer> subst, IntAllocator allocator, Map<TermNode, Deque<Edge>> trajectorie,
			TermDAG dag, Set<TermNode> newConstants) {
		Set<TermNode> constants = new HashSet<TermNode>();
		Set<TermNode> variables = new HashSet<TermNode>();
		
		for(TermNode n : trajectorie.keySet()) 
			if(n instanceof ConstTermNode || subst.keySet().contains(n) || n.isInRegister())
				constants.add(n);
			else 
				variables.add(n);
		
		Map<Edge, Integer> edgesToBind = new HashMap<Edge, Integer>();
		
		TermNode find = null;
		if(!constants.isEmpty()) {
			for(TermNode n : constants)
				if(find == null || trajectorie.get(find).size() < trajectorie.get(n).size())
					find = n;
			createReverseTrigger(converter, trajectorie.get(find), sequence, allocator, subst, edgesToBind, newConstants);
		}
		else {
			for(TermNode n : variables)
				if(find == null || trajectorie.get(find).size() < trajectorie.get(n).size())
					find = n;
			createFindTrigger(converter, trajectorie.get(find), sequence, allocator, subst, edgesToBind, newConstants);
		}
		
		Queue<Map<Edge, Integer>> bindQueue = new ConcurrentLinkedQueue<Map<Edge, Integer>>();
		bindQueue.add(edgesToBind);
		
		while(!bindQueue.isEmpty()) {
			Map<Edge, Integer> currentEdgesToBind = bindQueue.poll();
			
			for(Edge e : currentEdgesToBind.keySet()) {
				AppTermNode appTerm = (AppTermNode)e.m_To;
				Map<Edge, Integer> newEdgesToBind = bindEdge(converter, appTerm, subst, sequence, allocator, currentEdgesToBind.get(e));
				if(!newEdgesToBind.isEmpty())
					bindQueue.add(newEdgesToBind);
			}
		}
	}
	
	private void createFindTrigger(ConvertFormula converter, Deque<Edge> trajectorie, InsnSequence sequence, IntAllocator allocator,
			Map<TermVariable, Integer> subst, Map<Edge, Integer> edgesToBind, Set<TermNode> newConstants) {
		Edge edge = trajectorie.poll();
		AppTermNode find = (AppTermNode)edge.m_From;
		if(!find.isInRegister()) {
			int reg[];
			if(isNodeNeeded(find)) { 
				reg = allocator.alloc(find.getChildCount() + 1);
				newConstants.add(find);
			}
			else {
				reg = new int[find.getChildCount() + 1];
				int allocReg[] = allocator.alloc(find.getChildCount());
				reg[0] = -1;
				for(int i = 1; i < reg.length; i++) 
					reg[i] = allocReg[i - 1];
			}
			FindTrigger trig = new FindTrigger(converter.cclosure, find.getSymbol(), reg);
			sequence.append(trig);
			createCompares(converter, find, reg, -1, allocator, sequence, subst, edgesToBind);
		}
		createReverseTrigger(converter, trajectorie, sequence, allocator, subst, edgesToBind, newConstants);
	}
	
	private void createReverseTrigger(ConvertFormula converter, Deque<Edge> trajectorie, InsnSequence sequence, 
			IntAllocator allocator, Map<TermVariable, Integer> subst, Map<Edge, Integer> edgesToBind, 
			Set<TermNode> newConstants) {

		Set<TermNode> uselessConstants = new HashSet<TermNode>();
		for(TermNode app : newConstants)
			if(!isNodeNeeded(app)) {
				uselessConstants.add(app);
				allocator.free(app.getRegPos());
				app.setRegPos(-2);
			}
		newConstants.removeAll(uselessConstants);
		if (trajectorie.isEmpty())
			return;
		Edge reverseEdge = trajectorie.poll();
		TermNode constant = reverseEdge.m_To;
		assert(constant.isInRegister());
		AppTermNode parent = (AppTermNode)reverseEdge.m_From;
		if(!parent.isInRegister()) {
			int reg[] = new int[parent.getChildCount()];
			int allocReg[] = allocator.alloc(parent.getChildCount());
			int j = 0;
			if(isNodeNeeded(parent)) {
				reg[0] = allocReg[j];
				j++;
				newConstants.add(parent);
			} else 
				reg[0] = -1;
			for(int i = 1; i < reg.length; i++) {
				reg[i] = allocReg[j];
				j++;
			}
			for(int i = j; i < allocReg.length; i++)
				allocator.free(allocReg[i]);
			ReverseTrigger revTrig = new ReverseTrigger(converter.cclosure, parent.getSymbol(),
					reverseEdge.m_Num, constant.getRegPos(), reg, null);
			sequence.append(revTrig);
			createCompares(converter, parent, reg, reverseEdge.m_Num, allocator, sequence, subst, edgesToBind);
		}
		createReverseTrigger(converter, trajectorie, sequence, allocator, subst, edgesToBind, newConstants);
	}
	
	private void createCompares(ConvertFormula converter, TermNode currentNode, int[] reg, int skippedReg,
			IntAllocator allocator, InsnSequence sequence, Map<TermVariable, Integer> subst, 
			Map<Edge, Integer> edgesToBind){
		currentNode.setRegPos(reg[0]);
		List<Edge> children = currentNode.m_Outgoing;
		assert(children.size() <= reg.length);
		// Iterate over all outgoing edges
		for(int i = 0, regIdx = 1; i < children.size(); i++) {
			Edge edge = children.get(i);
			edge.mark();
			if (i == skippedReg)
				continue;
			if(reg[regIdx] != -1) {
				TermNode child = edge.m_To;
				if(child instanceof VarNode) {
					VarNode var = (VarNode)child;
					if(subst.containsKey(var.getVariable())) {
						int regVar = subst.get(var.getVariable());
						sequence.append(new CompareTrigger(regVar, reg[regIdx]));
						if(regVar > reg[regIdx]) {
							var.setRegPos(reg[regIdx]);
							subst.remove(var.getVariable());
							subst.put(var.getVariable(), reg[regIdx]);
							allocator.free(regVar);
						} else 
							allocator.free(reg[regIdx]);
					} else {
						subst.put(var.getVariable(), reg[regIdx]);
						var.setRegPos(reg[regIdx]);
					}
				} else if(child.isInRegister()) {
					sequence.append(new CompareTrigger(child.getRegPos(), reg[regIdx]));
					allocator.free(reg[regIdx]);
				} else {
					if(edgesToBind.keySet().contains(edge)) {
						sequence.append(new CompareTrigger(edgesToBind.get(edge), reg[regIdx]));
						allocator.free(reg[regIdx]);
					} else {
						edgesToBind.put(edge, reg[regIdx]);
						child.setRegPos(reg[regIdx]);
					}
				}
			}
			regIdx++;
		}
	}
	
	private Map<TermNode, Map<TermNode, Deque<Edge>>> findLongestPaths(Set<TermNode> roots, Set<TermNode> leafs) {
		assert(!leafs.isEmpty());
		assert(!roots.isEmpty());
		
		// Map<Root, Map<Leaf, Stack<Edge>>>
		Map<TermNode, Map<TermNode, Deque<Edge>>> longestPaths = 
			new HashMap<TermNode, Map<TermNode, Deque<Edge>>>();
		
		Map<TermNode, Set<Deque<Edge>>> currentTrajectories = 
			new HashMap<TermNode, Set<Deque<Edge>>>();
		
		for(TermNode leaf : leafs) {
			Set<Deque<Edge>> trajectories = new HashSet<Deque<Edge>>();
			for(Edge incommingEdge : leaf.m_Incomming) {
				Deque<Edge> deque = new ArrayDeque<Edge>();
				deque.add(incommingEdge);
				trajectories.add(deque);
			}
			currentTrajectories.put(leaf, trajectories);
		}
		
		while(!currentTrajectories.isEmpty()) {
			Map<TermNode, Set<Deque<Edge>>> nextTrajectories = 
				new HashMap<TermNode, Set<Deque<Edge>>>();
			
			for(TermNode leaf : currentTrajectories.keySet()) {
				Set<Deque<Edge>> nextSet = new HashSet<Deque<Edge>>();				
				for(Deque<Edge> cDeque : currentTrajectories.get(leaf)) {
					Edge cEdge = cDeque.peekLast();
					TermNode cNode = cEdge.m_From;
					if(roots.contains(cNode)) {
						Map<TermNode, Deque<Edge>> m = longestPaths.get(cNode);
						if(m == null) {
							m = new HashMap<TermNode, Deque<Edge>>();
							longestPaths.put(cNode, m);
						}
						Deque<Edge> s = m.get(leaf);
						if(s == null || s.size() < cDeque.size()) {
							m.remove(leaf);
							m.put(leaf, cDeque);
						}		
					} else 
						for(Edge nEdge : cNode.m_Incomming) {
							Deque<Edge> nextDeque = new ArrayDeque<Edge>(cDeque);
							nextDeque.add(nEdge);
							nextSet.add(nextDeque);
						}
				}
				if (!nextSet.isEmpty())
					nextTrajectories.put(leaf, nextSet);
			}
			currentTrajectories = nextTrajectories;
		}
		
		return longestPaths;
	}
	
	private Map<Edge, Integer> bindEdge(ConvertFormula converter, AppTermNode trigger, Map<TermVariable, Integer> subst, 
			InsnSequence sequence, IntAllocator allocator, int reg) {
		int[] allocReg = allocator.alloc(trigger.getChildCount() + 1);
		
		Map<Edge, Integer> edgesToBind = new HashMap<Edge, Integer>();
		BindTrigger trig = new BindTrigger(converter.cclosure, reg, trigger.getSymbol(), allocReg);
		sequence.append(trig);
		createCompares(converter, trigger, allocReg, -1, allocator, sequence, subst, edgesToBind);
		
		return edgesToBind;
	}
	
	/**
	 * @param node TermNode
	 * @return false if each incomming edge from node is marked, otherwise true
	 */
	private boolean isNodeNeeded(TermNode node) {
		for(Edge incomming : node.getIncomming())
			if(!incomming.isMarked())
				return true;
		return false;
	}
}
