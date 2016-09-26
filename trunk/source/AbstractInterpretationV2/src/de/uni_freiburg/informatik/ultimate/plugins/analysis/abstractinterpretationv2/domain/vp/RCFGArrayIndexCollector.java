/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Create and collects @EqNode from ApplicationTerm (store and select)
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class RCFGArrayIndexCollector extends RCFGEdgeVisitor {

	private final Set<EqGraphNode> eqGraphNodeSet = new HashSet<EqGraphNode>();
	private final Map<Term, EqBaseNode> termToBaseNodeMap = new HashMap<>();
	private final Map<Term, Set<EqFunctionNode>> termToFnNodeMap = new HashMap<>();
	private final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = new HashMap<>();

	private final Script mScript;

	public RCFGArrayIndexCollector(final RootNode root) {
		mScript = root.getRootAnnot().getScript();
		process(root.getOutgoingEdges());
	}

	private <T extends RCFGEdge> void process(final Collection<T> edges) {
		final Deque<RCFGEdge> worklist = new ArrayDeque<RCFGEdge>();
		final Set<RCFGEdge> finished = new HashSet<RCFGEdge>();

		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final RCFGEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			visit(current);
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}

	@Override
	protected void visit(CodeBlock c) {
		c.getPrettyPrintedStatements();

		final Set<Term[]> argsSet = new EqNodeFinder().findEqNode(c.getTransitionFormula().getFormula());
		final Iterator<Term[]> argsSetIter = argsSet.iterator();

		Term[] args;

		Map<Term, Term> substitionMap = new HashMap<Term, Term>();
		for (Entry<IProgramVar, TermVariable> entry : c.getTransitionFormula().getInVars().entrySet()) {
			substitionMap.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		for (Entry<IProgramVar, TermVariable> entry : c.getTransitionFormula().getOutVars().entrySet()) {
			substitionMap.put(entry.getValue(), entry.getKey().getTermVariable());
		}

		Term subArg0, subArg1, subArg2;
		EqNode subArg1Node;

		while (argsSetIter.hasNext()) {
			args = argsSetIter.next();

			subArg0 = new Substitution(mScript, substitionMap).transform(args[0]);
			subArg1 = new Substitution(mScript, substitionMap).transform(args[1]);

			subArg1Node = createNodeAndConnection(subArg1, null);
			createNodeAndConnection(subArg0, subArg1Node);

			if (args.length == 3) {
				subArg2 = new Substitution(mScript, substitionMap).transform(args[2]);

				createNodeAndConnection(subArg2, null);
			}
		}
	}

	private EqNode createNodeAndConnection(Term term, EqNode arg) {
		
		if (arg == null) {
			return getEqBaseNode(term);
		} else {
			return getEqFnNode(term, arg);
		}			
	}

	/**
	 * 
	 * @param term
	 * @return
	 */
	private EqBaseNode getEqBaseNode(Term term) {
		
		if (termToBaseNodeMap.containsKey(term)) {
			return termToBaseNodeMap.get(term);
		}
		
		EqBaseNode baseNode = new EqBaseNode(term);
		termToBaseNodeMap.put(term, baseNode);
		
		putToEqGraphSet(baseNode, null);		
		return baseNode;
	}
	
	private EqFunctionNode getEqFnNode(Term term, EqNode arg) {
		
		if (termToFnNodeMap.containsKey(term)) {
			for (EqFunctionNode fnNode : termToFnNodeMap.get(term)) {
				if (fnNode.getArg().term.equals(arg.term)) {
					return fnNode;
				}
			}			
		}
			
		EqFunctionNode fnNode = new EqFunctionNode(term, arg);
		if (termToFnNodeMap.get(term) == null) {
			termToFnNodeMap.put(term, new HashSet<EqFunctionNode>());
		}
		termToFnNodeMap.get(term).add(fnNode);
		putToEqGraphSet(fnNode, arg);
			
		return fnNode;
		
	}
	
	private void putToEqGraphSet(EqNode node, EqNode arg) {
		EqGraphNode graphNode = new EqGraphNode(node);
		
		if (arg != null) {
			graphNode.setArg(arg);
			eqNodeToEqGraphNodeMap.get(arg).getCcpar().add(node);
		}
		
		eqGraphNodeSet.add(graphNode);
		eqNodeToEqGraphNodeMap.put(node, graphNode);
		
	}

	public Set<EqGraphNode> getEqGraphNodeSet() {
		return eqGraphNodeSet;
	}

	public Map<Term, EqBaseNode> getTermToBaseNodeMap() {
		return termToBaseNodeMap;
	}

	public Map<Term, Set<EqFunctionNode>> getTermToFnNodeMap() {
		return termToFnNodeMap;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return eqNodeToEqGraphNodeMap;
	}

	@Override
	public String toString() {
		return "";
	}


}