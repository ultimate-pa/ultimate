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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Create and collects @EqNode from ApplicationTerm (store and select)
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class RCFGArrayIndexCollector extends RCFGEdgeVisitor {
	
	private static final String TERM_FUNC_NAME_SELECT = "select";

	private final Map<Term, EqBaseNode> termToBaseNodeMap = new HashMap<>();
	private final Map<Term, Set<EqFunctionNode>> termToFnNodeMap = new HashMap<>();
	private final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = new HashMap<>();
	
	private final Map<Term, EqNode> mTermToEqNode = new HashMap<>();

	Map<Term, BoogieVarOrConst> mTermToBoogieVarOrConst = new HashMap<>();

	private final Script mScript;

	private final Boogie2SMT mBoogie2SMT;

	private final NestedMap2<BoogieVarOrConst, List<EqNode>, EqFunctionNode> mEqFunctionNodeStore = new NestedMap2<>();
	private final Map<BoogieVarOrConst, EqBaseNode> mEqBaseNodeStore = new HashMap<>();

	public RCFGArrayIndexCollector(final BoogieIcfgContainer root) {
		mScript = root.getCfgSmtToolkit().getManagedScript().getScript();
		mBoogie2SMT = root.getBoogie2SMT();
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
		
		final Term transFormulaTerm = c.getTransitionFormula().getFormula();
		final Term formulaWithNormalizedVariables = new Substitution(mScript, substitionMap).transform(transFormulaTerm);
		
		// handle selects in the formula
		List<MultiDimensionalSelect> mdSelects = MultiDimensionalSelect.extractSelectShallow(formulaWithNormalizedVariables, false);
		for (MultiDimensionalSelect mds : mdSelects) {
			getOrConstructEqNode(mds);
		}
		
		// handle stores in the formula
		List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresShallow(formulaWithNormalizedVariables);
		for (MultiDimensionalStore mds : mdStores) {
			getOrConstructEqNode(mds);
		}

		// handle TermVariables and constants that are equated to a select
		Set<String> equationFunctionNames = new HashSet<String>(2);
		equationFunctionNames.add("=");
		equationFunctionNames.add("distinct");
		Set<ApplicationTerm> equations = 
				new ApplicationTermFinder(equationFunctionNames, false)
					.findMatchingSubterms(formulaWithNormalizedVariables);
		Set<Term> selectTerms = mdSelects.stream().map(mds -> mds.getSelectTerm()).collect(Collectors.toSet());
		Set<Term> termsEquatedWithASelectTerm = new HashSet<>();
		for (ApplicationTerm eq : equations) {
			if (selectTerms.contains(eq.getParameters()[0])
					&& !selectTerms.contains(eq.getParameters()[1])) {
				termsEquatedWithASelectTerm.add(eq.getParameters()[1]);
			} else if (selectTerms.contains(eq.getParameters()[1])
					&& !selectTerms.contains(eq.getParameters()[0])) {
				termsEquatedWithASelectTerm.add(eq.getParameters()[0]);
			}
		}
		for (Term t : termsEquatedWithASelectTerm) {
			getOrConstructEqNode(t);
		}
	}
	
	private EqNode getOrConstructEqNode(MultiDimensionalStore mds) {
		// TODO
		EqNode result = mTermToEqNode.get(mds.getStoreTerm());
		if (result != null) {
			return result;
		}
		
		List<EqNode> arguments = new ArrayList<>();
		for (Term ai : mds.getIndex()) {
			arguments.add(getOrConstructEqNode(ai));
		}
		getOrConstructEqNode(mds.getValue());

		Term array = mds.getArray();
		result = getOrConstructEqFnNode(getOrConstructBoogieVarOrConst(array), arguments);
		mTermToEqNode.put(mds.getStoreTerm(), result);
		return result;
	}

	private EqNode getOrConstructEqNode(MultiDimensionalSelect mds) {
		EqNode result = mTermToEqNode.get(mds.getSelectTerm());
		if (result != null) {
			return result;
		}
		
		Term array = mds.getArray();
		List<EqNode> arguments = new ArrayList<>();
		for (Term ai : mds.getIndex()) {
			arguments.add(getOrConstructEqNode(ai));
		}

		result = getOrConstructEqFnNode(getOrConstructBoogieVarOrConst(array),
				arguments);
		mTermToEqNode.put(mds.getSelectTerm(), result);
		return result;
	}

	private EqNode getOrConstructEqNode(Term t) {
		EqNode result = mTermToEqNode.get(t);
		if (result != null) {
			return result;
		}
		// we need to construct a fresh EqNode
		if (t instanceof TermVariable 
				|| t instanceof ConstantTerm
				|| (t instanceof ApplicationTerm && ((ApplicationTerm) t).getParameters().length == 0)) {
			result = getOrConstructEqBaseNode(getOrConstructBoogieVarOrConst(t));
			mTermToEqNode.put(t, result);
			return result;
		} 
		// we need to construct an EqFunctionNode	
		assert t instanceof ApplicationTerm;
		ApplicationTerm at = (ApplicationTerm) t;
		if (at.getFunction().getName() == "select") {
			MultiDimensionalSelect mds = new MultiDimensionalSelect(at);
			return getOrConstructEqNode(mds);
		} else if (at.getFunction().getName() == "store") {
			MultiDimensionalStore mds = new MultiDimensionalStore(at);
			return getOrConstructEqNode(mds);
		} else {
			assert false : "should not happen";
			return null;
		}
	}
	
	private BoogieVarOrConst getOrConstructBoogieVarOrConst(final Term t) {
		BoogieVarOrConst result = mTermToBoogieVarOrConst.get(t);
		if (result != null) {
			return result;
		}
		
		if (t instanceof ApplicationTerm ) {
			assert ((ApplicationTerm) t).getParameters().length == 0 : "not a constant";
			BoogieConst bc = mBoogie2SMT.getBoogie2SmtSymbolTable().getBoogieConst((ApplicationTerm) t);
			result = new BoogieVarOrConst(bc);
		} else if (t instanceof ConstantTerm) {
			result = new BoogieVarOrConst((ConstantTerm) t);
		} else if (t instanceof TermVariable) {
			IProgramVar pv = mBoogie2SMT.getBoogie2SmtSymbolTable().getBoogieVar((TermVariable) t);
			assert pv != null : "?";
			result = new BoogieVarOrConst(pv);
		} else {
			assert false;
			return null;
		}
		mTermToBoogieVarOrConst.put(t, result);
		return result;
	}
	
	/**
	 * 
	 * @param tv
	 * @return
	 */
	private EqBaseNode getOrConstructEqBaseNode(final BoogieVarOrConst bv) {
		
		EqBaseNode result = mEqBaseNodeStore.get(bv);
		
		if (result == null) {
			result = new EqBaseNode(bv);
			mEqBaseNodeStore.put(bv, result);
			putToEqGraphSet(result, null);		
		}
		return result;
	}
	
	private EqFunctionNode getOrConstructEqFnNode(final BoogieVarOrConst eqNode, final List<EqNode> indices) {
			
		EqFunctionNode result = mEqFunctionNodeStore.get(eqNode, indices);
		if (result == null) {
			result = new EqFunctionNode(eqNode, indices);

			mEqFunctionNodeStore.put(eqNode, indices, result);
			putToEqGraphSet(result, indices);
		}
		return result;
	}

	private void putToEqGraphSet(final EqNode node, final List<EqNode> args) {
		final EqGraphNode graphNode = new EqGraphNode(node);
		List<EqGraphNode> argNodes = new ArrayList<>();
		
		if (args != null) {
			assert !args.isEmpty();
			graphNode.setArgs(args);
			for (EqNode arg : args) {
				EqGraphNode argNode = eqNodeToEqGraphNodeMap.get(arg);
				argNode.addToInitCcpar(node);
				argNode.addToCcpar(node);
				argNodes.add(argNode);
			}
			graphNode.setInitCcchild(args);
			graphNode.getCcchild().add(args);
		}
		
		eqNodeToEqGraphNodeMap.put(node, graphNode);
	}

	public Set<EqGraphNode> getEqGraphNodeSet() {
		return new HashSet<EqGraphNode>(eqNodeToEqGraphNodeMap.values());
	}

	public Map<Term, EqBaseNode> getTermToBaseNodeMap() {
		assert false : "probably not filled correctly";
		return termToBaseNodeMap;
	}

	public Map<Term, Set<EqFunctionNode>> getTermToFnNodeMap() {
		assert false : "probably not filled correctly";
		return termToFnNodeMap;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		assert false : "probably not filled correctly";
		return eqNodeToEqGraphNodeMap;
	}
	
	@Override
	public String toString() {
		return "-RCFGArrayIndexCollector-";
	}

	public Map<Term, EqNode> getTermToEqNodeMap() {
		return mTermToEqNode;
	}


}