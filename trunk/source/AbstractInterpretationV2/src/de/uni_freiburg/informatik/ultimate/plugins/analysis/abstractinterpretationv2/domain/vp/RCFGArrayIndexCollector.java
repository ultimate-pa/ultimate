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

	private final Set<EqNode> eqNodeSet = new HashSet<EqNode>();
	private final Map<Term, EqBaseNode> termToBaseNodeMap = new HashMap<>();
	private final Map<Term, Map<Term, EqFunctionNode>> termToFunctionNodeMap = new HashMap<>();

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

		while (argsSetIter.hasNext()) {
			args = argsSetIter.next();

			subArg0 = new Substitution(mScript, substitionMap).transform(args[0]);
			subArg1 = new Substitution(mScript, substitionMap).transform(args[1]);

			addNodeToSet(subArg0, subArg1);

			addNodeToSet(subArg1, null);

			if (args.length == 3) {
				subArg2 = new Substitution(mScript, substitionMap).transform(args[2]);

				addNodeToSet(subArg2, null);
			}
		}
	}

	private void addNodeToSet(Term term, Term arg) {
		if (arg != null) {
			eqNodeSet.add(getFunctionNode(term, arg));
		} else {
			eqNodeSet.add(getBaseNode(term));
		}
	}

	/**
	 * Check if the term already have a @EqBaseNode in eqNodeSet. If yes, return
	 * null. If not, return a new @EqBaseNode.
	 * 
	 * @param term
	 * @return
	 */
	private EqBaseNode getBaseNode(Term term) {
		
		if (termToBaseNodeMap.containsKey(term)) {
			return termToBaseNodeMap.get(term);
		}
		
		EqBaseNode baseNode = new EqBaseNode(term);
		termToBaseNodeMap.put(term, baseNode);
		return baseNode;
	}

	/**
	 * Check if the term already have a @EqFunctionNode in eqNodeSet. If yes, return
	 * null. If not, return a new @EqFunctionNode.
	 * 
	 * @param function
	 * @param arg
	 * @return
	 */
	private EqFunctionNode getFunctionNode(Term function, Term arg) {
		
		EqBaseNode baseNode = getBaseNode(arg);
		EqFunctionNode functionNode = new EqFunctionNode(function, baseNode);
		
		if (termToFunctionNodeMap.containsKey(function)) {
			for (Entry<Term, EqFunctionNode> fnNode : termToFunctionNodeMap.get(function).entrySet()) {
				if (fnNode.getKey().equals(arg)) {
					return fnNode.getValue();
				}
			}
			termToFunctionNodeMap.get(function).put(arg, functionNode);
			return functionNode;
		}
		
		Map<Term, EqFunctionNode> map = new HashMap<>();
		map.put(arg, functionNode);
		termToFunctionNodeMap.put(function, map);
		return functionNode;
	}

	@Override
	public String toString() {
		return "";
	}

	public Set<EqNode> getEqNodeSet() {
		return eqNodeSet;
	}

	public Map<Term, EqBaseNode> getTermToBaseNodeMap() {
		return termToBaseNodeMap;
	}

	public Map<Term, Map<Term, EqFunctionNode>> getTermToFunctionNodeMap() {
		return termToFunctionNodeMap;
	}


}