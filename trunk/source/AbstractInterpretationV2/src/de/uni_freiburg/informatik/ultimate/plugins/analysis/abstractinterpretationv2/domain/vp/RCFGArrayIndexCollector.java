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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Create and collects @EqNode from ApplicationTerm (store and select)
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class RCFGArrayIndexCollector extends RCFGEdgeVisitor {
	
	private static final String TERM_FUNC_NAME_SELECT = "select";

	private final Set<EqGraphNode> eqGraphNodeSet = new HashSet<EqGraphNode>();
	private final Map<Term, EqBaseNode> termToBaseNodeMap = new HashMap<>();
	private final Map<Term, Set<EqFunctionNode>> termToFnNodeMap = new HashMap<>();
	private final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = new HashMap<>();

	private final Script mScript;

	public RCFGArrayIndexCollector(final BoogieIcfgContainer root) {
		mScript = root.getCfgSmtToolkit().getManagedScript().getScript();
		process(BoogieIcfgContainer.extractStartEdges(root));
	}

	private <T extends IcfgEdge> void process(final Collection<T> edges) {
		final Deque<IcfgEdge> worklist = new ArrayDeque<IcfgEdge>();
		final Set<IcfgEdge> finished = new HashSet<IcfgEdge>();
		
		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final IcfgEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			visit(current);
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}

	@Override
	protected void visit(final CodeBlock c) {
		c.getPrettyPrintedStatements();
		
		final Map<Term, Term> substitionMap = new HashMap<Term, Term>();
		for (final Entry<IProgramVar, TermVariable> entry : c.getTransitionFormula().getInVars().entrySet()) {
			substitionMap.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		for (final Entry<IProgramVar, TermVariable> entry : c.getTransitionFormula().getOutVars().entrySet()) {
			substitionMap.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		
		final Term transFormedTerm = new Substitution(mScript, substitionMap).transform(c.getTransitionFormula().getFormula());
		final List<EqNodeFinder.SelectOrStoreArguments> argsList = new EqNodeFinder().findEqNode(transFormedTerm);

		Term array, index, element;
		int argsListSize = argsList.size();
		EqNodeFinder.SelectOrStoreArguments selOrStore;
		
		for (int i = argsListSize - 1; i >= 0; i--) {
			
			selOrStore = argsList.get(i);

			array = selOrStore.function;
			index = selOrStore.arg;			
			if (selOrStore instanceof EqNodeFinder.StoreArguments) {
				element = ((EqNodeFinder.StoreArguments) selOrStore).arg2;
			} else {
				element = null;
			}
			
			createNode(array, indexAndElementHandler(index));
			if (element != null) {
				indexAndElementHandler(element);
			}
		}
	}
	
	private EqNode indexAndElementHandler(final Term index) {
				
		if (index instanceof TermVariable || index instanceof ConstantTerm) {
			return createNode(index, null);
		} else if (index instanceof ApplicationTerm) {
			return getAppNode((ApplicationTerm)index);
		}
		
		return null;
	}
	
	private EqNode createNode(final Term term, final EqNode arg) {
		
		if (arg == null) {
			return getEqBaseNode(term);
		} else {
			return getEqFnNode(term, arg);
		}			
	}

	private EqNode getAppNode(ApplicationTerm appTerm) {
		if (appTerm.getParameters()[1] instanceof ApplicationTerm) {
			return getEqFnNode(appTerm.getParameters()[0], getAppNode((ApplicationTerm)appTerm.getParameters()[1]));
		} else {
			return getEqFnNode(appTerm.getParameters()[0], getEqBaseNode(appTerm.getParameters()[1]));
		}
	}
	
	/**
	 * 
	 * @param term
	 * @return
	 */
	private EqBaseNode getEqBaseNode(final Term term) {
		
		if (termToBaseNodeMap.containsKey(term)) {
			return termToBaseNodeMap.get(term);
		}
		
		final EqBaseNode baseNode = new EqBaseNode(term);
		termToBaseNodeMap.put(term, baseNode);
		
		putToEqGraphSet(baseNode, null);		
		return baseNode;
	}
	
	private EqFunctionNode getEqFnNode(final Term function, final EqNode arg) {
		
		if (termToFnNodeMap.containsKey(function)) {
			for (final EqFunctionNode fnNode : termToFnNodeMap.get(function)) {
				if (fnNode.getArg().equals(arg)) {
					return fnNode;
				}
			}			
		}
			
		final EqFunctionNode fnNode = new EqFunctionNode(getArraySelectTerm(function, arg.getTerm()), function, arg);
		if (!termToFnNodeMap.containsKey(function)) {
			termToFnNodeMap.put(function, new HashSet<EqFunctionNode>());
		}
		termToFnNodeMap.get(function).add(fnNode);
		putToEqGraphSet(fnNode, arg);
		
		return fnNode;
		
	}
	
	private Term getArraySelectTerm(Term array, Term index) {
		return mScript.term(TERM_FUNC_NAME_SELECT, array, index);
	}
	
	private void putToEqGraphSet(final EqNode node, final EqNode arg) {
		final EqGraphNode graphNode = new EqGraphNode(node);
		EqGraphNode argNode = null;
		
		if (arg != null) {
			graphNode.setArg(arg);
			argNode = eqNodeToEqGraphNodeMap.get(arg);
			argNode.addToInitCcpar(node);
			argNode.addToCcpar(node);
		}
		
		if (argNode != null) {
			graphNode.setInitCcchild(argNode.eqNode);
			graphNode.getCcchild().add(argNode.eqNode);
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