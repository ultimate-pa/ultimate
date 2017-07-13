/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqConstraint<ACTION extends IIcfgTransition<IcfgLocation>, 
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	private boolean mIsFrozen = false;

	CongruenceGraph<ACTION, NODE, FUNCTION> mElementCongruenceGraph;

	ArrayEquivalenceGraph<ACTION, NODE, FUNCTION> mFunctionEquivalenceGraph;

	private EqConstraintFactory<ACTION, NODE, FUNCTION> mFactory;

	private boolean mIsVersioned;

	private Set<IProgramVar> mVariables;
	private Set<IProgramVarOrConst> mPvocs;

	private Term mTerm;

	/**
	 * All (element) nodes that this constraint currently knows about
	 */
	private final Set<NODE> mNodes;

	private final Set<FUNCTION> mFunctions;

	/**
	 * Creates an empty constraint (i.e. it does not constrain anything, is
	 * equivalent to "true")
	 * 
	 * @param factory
	 */
	public EqConstraint(EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		mFactory = factory;

		mNodes = new HashSet<>();
		mFunctions = new HashSet<>();

		mElementCongruenceGraph = new CongruenceGraph<>(this);
		mFunctionEquivalenceGraph = new ArrayEquivalenceGraph<>(this);

	}

	/**
	 * copy constructor
	 * 
	 * @param constraint
	 */
	public EqConstraint(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		mFactory = constraint.mFactory;
		mNodes = new HashSet<>(constraint.mNodes);
		mFunctions = new HashSet<>(constraint.mFunctions);

		mElementCongruenceGraph = new CongruenceGraph<>(constraint.mElementCongruenceGraph, this);

		// copy the union find containing array equalities
		mFunctionEquivalenceGraph = new ArrayEquivalenceGraph<>(constraint.mFunctionEquivalenceGraph, this);

	}

	/**
	 * 
	 * @param node1
	 * @param node2
	 * @return The merge history, i.e., all pairs of former representatives that
	 *         have been merged by this merge operation
	 */
	public HashRelation<NODE, NODE> merge(NODE node1, NODE node2) {
		return mElementCongruenceGraph.merge(node1, node2);
	}

	public void havoc(NODE node) {
		assert !mIsFrozen;
		if (!mNodes.contains(node) || isBottom()) {
			assert VPDomainHelpers.constraintFreeOfVars(Arrays.asList(node.getTerm().getFreeVars()), 
					this, 
					mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) : 
						"resulting constraint still has at least one of the to-be-projected vars";
			return;
		}

		mElementCongruenceGraph.havoc(node);
	}

	public void havocFunction(FUNCTION func) {
		assert !mIsFrozen;

		if (!mFunctions.contains(func) || isBottom()) {
			return;
		}

		mFunctionEquivalenceGraph.havocFunction(func);
		assert !getAllFunctions().contains(func);
	}

	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
		mElementCongruenceGraph.freeze();
		mFunctionEquivalenceGraph.freeze();
		assert allNodesAndEqgnMapAreConsistent();
		// mFunctionDisequalities =
		// Collections.unmodifiableSet(mFunctionDisequalities);
	}

	public boolean isBottom() {
		return false;
	}

	public Set<NODE> getAllNodes() {
		return Collections.unmodifiableSet(mNodes);
	}

	// public void addNodes(Collection<NODE> allNodes) {
	// mElementCongruenceGraph.addNodes(allNodes);
	// }

	public HashRelation<NODE, NODE> getSupportingElementEqualities() {
		return mElementCongruenceGraph.getSupportingEqualities();
	}

	public Set<VPDomainSymmetricPair<NODE>> getElementDisequalities() {
		return mElementCongruenceGraph.getDisequalities();
	}

	/**
	 * "Raw" means here that the disequality is not yet normalized such that it
	 * only speaks about equivalence representatives.
	 * 
	 * @param first
	 * @param second
	 */
	public void addRawDisequality(NODE first, NODE second) {
		assert !mIsFrozen;
		mElementCongruenceGraph.addDisequality(mElementCongruenceGraph.find(first),
				mElementCongruenceGraph.find(second));
	}

	public HashRelation<FUNCTION, FUNCTION> getSupportingFunctionEqualities() {
		/*
		 * plan: for each equivalence class, iterate over the elements and
		 * report an equality for each two consecutive elements
		 */
		HashRelation<FUNCTION, FUNCTION> result = new HashRelation<>();
		for (Set<FUNCTION> eqClass : mFunctionEquivalenceGraph.getAllEquivalenceClasses()) {
			FUNCTION lastElement;
			FUNCTION currentElement = null;
			for (FUNCTION el : eqClass) {
				lastElement = currentElement;
				currentElement = el;
				if (lastElement != null) {
					result.addPair(lastElement, currentElement);
				}
			}
		}

		return result;
	}

	public void addFunctionEqualityRaw(FUNCTION func1, FUNCTION func2) {
		assert !areUnequal(func1, func2) : "check before!?";
		// mFunctionEquivalenceGraph.union(mFunctionEquivalenceGraph.findAndConstructEquivalenceClassIfNeeded(func1),
		// mFunctionEquivalenceGraph.findAndConstructEquivalenceClassIfNeeded(func2));
		mFunctionEquivalenceGraph.union(func1, func2);

		// TODO: adding a function equality can have consequences for the
		// elements --> implement

		// nodesWithFunc.stream().forEach(node -> havoc(node));

	}

	public Set<VPDomainSymmetricPair<FUNCTION>> getFunctionDisequalites() {
		return mFunctionEquivalenceGraph.getFunctionDisequalities();
	}

	public void addFunctionDisequality(FUNCTION first, FUNCTION second) {
		// final FUNCTION firstRep = mFunctionEquivalenceGraph.find(first);
		// final FUNCTION secondRep = mFunctionEquivalenceGraph.find(second);

		// mFunctionDisequalities.add(new
		// VPDomainSymmetricPair<FUNCTION>(firstRep, secondRep));
		mFunctionEquivalenceGraph.addFunctionDisequality(first, second);
	}

	public boolean checkForContradiction() {
		if (mElementCongruenceGraph.checkContradiction()) {
			return true;
		}
		if (mFunctionEquivalenceGraph.checkContradiction()) {
			return true;
		}

		return false;
	}

	public boolean isFrozen() {
		return mIsFrozen;
	}

	/**
	 * 
	 * 
	 * TDO: should we also remove the nodes that we project, here?? edit: yes,
	 * havoc does remove the nodes
	 * 
	 * @param varsToProjectAway
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> projectExistentially(Set<TermVariable> varsToProjectAway) {
		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = mFactory.unfreeze(this);
		
		
		varsToProjectAway.forEach(var -> unfrozen.havoc(var));
		
//		for (TermVariable var : varsToProjectAway) {
//			unfrozen.havoc(var);
//		}
		unfrozen.freeze();
		assert VPDomainHelpers.constraintFreeOfVars(varsToProjectAway, unfrozen, 
				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) : 
					"resulting constraint still has at least one of the to-be-projected vars";

		return unfrozen;
	}


	private void havoc(TermVariable var) {
		
		final Set<NODE> nodesWithVar = getAllNodes().stream()
				.filter(n -> Arrays.asList(n.getTerm().getFreeVars()).contains(var)).collect(Collectors.toSet());
		final Set<FUNCTION> functionsWithVar = getAllFunctions().stream()
				.filter(f -> Arrays.asList(f.getTerm().getFreeVars()).contains(var)).collect(Collectors.toSet());
		
		nodesWithVar.forEach(f -> havoc(f));
		functionsWithVar.forEach(f -> havocFunction(f));
		assert VPDomainHelpers.constraintFreeOfVars(Collections.singleton(var), this, 
				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) : 
					"resulting constraint still has at least one of the to-be-projected vars";
	}

	private FUNCTION getFunctionForTerm(Term var) {
		return (FUNCTION) mFactory.getEqStateFactory().getEqNodeAndFunctionFactory().getExistingEqFunction(var);
	}

	private NODE getNodeForTerm(Term var) {
		return (NODE) mFactory.getEqStateFactory().getEqNodeAndFunctionFactory().getExistingEqNode(var);
	}

	public void renameVariables(Map<Term, Term> substitutionMapping) {
		assert !mIsFrozen;
		
		final Set<NODE> newNodes = mNodes.stream()
				.map(node -> node.renameVariables(substitutionMapping)).collect(Collectors.toSet());
		final Set<FUNCTION> newFunctions = mFunctions.stream()
				.map(node -> node.renameVariables(substitutionMapping)).collect(Collectors.toSet());
		
		mNodes.clear();
		mNodes.addAll(newNodes);
		
		mFunctions.clear();
		mFunctions.addAll(newFunctions);

		mElementCongruenceGraph.renameVariables(substitutionMapping);

		mFunctionEquivalenceGraph.renameVariables(substitutionMapping);
	}

	/**
	 * 
	 * @param node1
	 * @param node2
	 * @return true iff this constraint says "node1 and node2 must be equal"
	 */
	public boolean areEqual(NODE node1, NODE node2) {
		final NODE find1 = mElementCongruenceGraph.find(node1);
		final NODE find2 = mElementCongruenceGraph.find(node2);
		if (find1 == null || find2 == null) {
			// this constraint does not track at least one of the given nodes
			return false;
		}
		return find1.equals(find2);
	}

	public HashRelation<FUNCTION, List<NODE>> getCCChild(NODE representative1) {
		return mElementCongruenceGraph.getCCChild(representative1);
	}

	/**
	 * 
	 * @param node1
	 * @param node2
	 * @return true iff this constraint says "node1 and node2 must be unequal"
	 */
	public boolean areUnequal(NODE node1, NODE node2) {
		final NODE find1 = mElementCongruenceGraph.find(node1);
		final NODE find2 = mElementCongruenceGraph.find(node2);
		if (find1 == null || find2 == null) {
			// this constraint does not track at least one of the given nodes
			return false;
		}
		final VPDomainSymmetricPair<NODE> representativePair = new VPDomainSymmetricPair<>(find1, find2);
		return mElementCongruenceGraph.getDisequalities().contains(representativePair);
	}

	/**
	 * Returns all the equivalence representatives that the given node is
	 * unequal to in this constraint.
	 */
	public Set<NODE> getDisequalities(NODE node) {
		final Set<NODE> result = new HashSet<>();

		final NODE nodeRep = mElementCongruenceGraph.find(node);
		for (VPDomainSymmetricPair<NODE> deq : mElementCongruenceGraph.getDisequalities()) {
			if (deq.contains(nodeRep)) {
				result.add(deq.getOther(nodeRep));
			}
		}
		return result;
	}

	public Term getTerm(Script script) {
//		assert mIsFrozen : "not yet frozen, term may not be final..";
		if (mTerm != null) {
			return mTerm;
		}
		final List<Term> elementEqualities = getSupportingElementEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = getElementDisequalities().stream()
				.map(pair -> script.term("distinct", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionEqualities = getSupportingFunctionEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionDisequalities = getFunctionDisequalites().stream()
				.map(pair -> script.term("distinct", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
				.collect(Collectors.toList());

		final List<Term> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(elementEqualities);
		allConjuncts.addAll(elementDisequalities);
		allConjuncts.addAll(functionEqualities);
		allConjuncts.addAll(functionDisequalities);

		final Term result= Util.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		if (mIsFrozen) {
			mTerm = result;
		}
		return result;
	}

	public boolean areEqual(FUNCTION func1, FUNCTION func2) {
		return mFunctionEquivalenceGraph.areEqual(func1, func2);
	}

	public boolean areUnequal(FUNCTION func1, FUNCTION func2) {
		return mFunctionEquivalenceGraph.areUnequal(func1, func2);
	}

	/**
	 * This only really makes sense when this constraint is in a renaming state
	 * such that the TermVariables are "normalized" to the TermVariables that
	 * are associated to IProgramVars.
	 * 
	 * I.e. when it is the constraint of a EqPredicate or an EqState
	 * 
	 * @return
	 */
	public Set<IProgramVar> getVariables(IIcfgSymbolTable symbolTable) {
		assert mIsFrozen;
		if (mVariables == null) {
			Set<TermVariable> allTvs = new HashSet<>();
			mNodes.stream().forEach(node -> allTvs.addAll(Arrays.asList(node.getTerm().getFreeVars())));

			mFunctions.stream().forEach(func -> allTvs.addAll(Arrays.asList(func.getTerm().getFreeVars())));

			/*
			 * note this will probably crash if this method is called on an
			 * EqConstraint that does not belong to a predicate or state
			 */
			mVariables = allTvs.stream().map(tv -> symbolTable.getProgramVar(tv)).collect(Collectors.toSet());
		}

		return mVariables;
	}

	/**
	 * Collects the Pvocs (IprogramVarOrConsts) that are mentioned in this EqConstraint by looking up the TermVariables 
	 * and nullary ApplicationTerms in the symbol table. 
	 * 
	 * These Pvocs correspond to the Pvocs of the compacted version of an EqState that has this constraint, i.e.,
	 * only Pvocs that are actually constrained by this constraint are mentioned.
	 * 
	 * We expect this to only be called when this constraint is the constraint
	 * of an EqState, thus we expect all TermVariables to correspond to an IProgramVar and all nullary ApplicationTerms
	 * to correspond to a constant that is mentioned in the symbol table.
	 * 
	 * @param symbolTable
	 * 
	 * @return
	 */
	public Set<IProgramVarOrConst> getPvocs(IIcfgSymbolTable symbolTable) {
		assert mIsFrozen;
		if (mPvocs == null) {
			mPvocs = new HashSet<>();
			mPvocs.addAll(getVariables(symbolTable));

			final Set<ApplicationTerm> constants = new HashSet<>();
			mNodes.stream()
					.forEach(node -> constants.addAll(new ConstantFinder().findConstants(node.getTerm(), false)));
			// TODO do we need to find literals here, too?? (i.e. ConstantTerms)

			mFunctions.stream()
					.forEach(func -> constants.addAll(new ConstantFinder().findConstants(func.getTerm(), false)));

			mPvocs.addAll(constants.stream().map(c -> symbolTable.getProgramConst(c)).collect(Collectors.toSet()));
		}
		return mPvocs;
	}

	/**
	 * all equalities that hold in this constraint (transitive, symmetric
	 * closure)
	 * 
	 * @return
	 */
	public Set<VPDomainSymmetricPair<NODE>> getAllElementEqualities() {
		final Set<VPDomainSymmetricPair<NODE>> result = new HashSet<>();
		final List<NODE> allNodes = new ArrayList<>(getAllNodes());
		for (int i = 0; i < allNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				if (areEqual(allNodes.get(i), allNodes.get(j))) {
					result.add(new VPDomainSymmetricPair<NODE>(allNodes.get(i), allNodes.get(j)));
				}
			}
		}
		return result;
	}

	/**
	 * (expensive)
	 * @return all disequalities (as symmetric pairs) that hold in this state, i.e., not only those over representatives
	 */
	public Set<VPDomainSymmetricPair<NODE>> getAllElementDisequalities() {
		final Set<VPDomainSymmetricPair<NODE>> result = new HashSet<>();
		final List<NODE> allNodes = new ArrayList<>(getAllNodes());
		for (int i = 0; i < allNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				if (areUnequal(allNodes.get(i), allNodes.get(j))) {
					result.add(new VPDomainSymmetricPair<NODE>(allNodes.get(i), allNodes.get(j)));
				}
			}
		}
		return result;
	}

	/**
	 * retrieves all equalities between functions that we know hold
	 * more precise:
	 *  - is transitively closed
	 *  - symmetrically closed through use of VPDomainSymmetricPair
	 *  - does not explicitly account for reflexivity
	 * @return
	 */
	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionEqualities() {
		return mFunctionEquivalenceGraph.getAllFunctionEqualities();
	}

	/**
	 * analogue to getAllFunctionEqualities, i.e. _all_ disequalities, not only the disequalities over representatives
	 * @return
	 */
	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionDisequalities() {
		return mFunctionEquivalenceGraph.getAllFunctionDisequalities();
	}

	@Override
	public String toString() {
		// (adapted from getTerm())
		final List<String> elementEqualities = getSupportingElementEqualities().entrySet().stream()
				.map(en -> String.format("(%s = %s)", en.getKey().getTerm().toStringDirect(), 
						en.getValue().getTerm().toStringDirect()))
				.collect(Collectors.toList());
		final List<String> elementDisequalities = getElementDisequalities().stream()
				.map(pair -> String.format("(%s != %s)", pair.getFirst().getTerm().toStringDirect(), 
						pair.getSecond().getTerm().toStringDirect()))
				.collect(Collectors.toList());
		final List<String> functionEqualities = getSupportingFunctionEqualities().entrySet().stream()
				.map(en -> String.format("(%s = %s)", en.getKey().getTerm().toStringDirect(), 
						en.getValue().getTerm().toStringDirect()))
				.collect(Collectors.toList());
		final List<String> functionDisequalities = getFunctionDisequalites().stream()
				.map(pair -> String.format("(%s != %s)", pair.getFirst().getTerm().toStringDirect(), 
						pair.getSecond().getTerm().toStringDirect()))
				.collect(Collectors.toList());

		final List<String> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(elementEqualities);
		allConjuncts.addAll(elementDisequalities);
		allConjuncts.addAll(functionEqualities);
		allConjuncts.addAll(functionDisequalities);

		if (allConjuncts.isEmpty()) {
			return "Top";
		}

		String sep = "";
		final StringBuilder sb = new StringBuilder();
		for (String s : allConjuncts) {
			sb.append(sep);
			sep = "\n";
			sb.append(s);
		}

		return sb.toString();
	}

	public boolean hasNode(NODE node) {
		return mNodes.contains(node);
	}

	/**
	 * Add a node to this constraint. Does not do any propagations that might be
	 * a consequence of adding this node.
	 * 
	 * @param nodeToAdd
	 */
	public void addNodeRaw(NODE nodeToAdd) {
		assert !mIsFrozen;
		if (hasNode(nodeToAdd)) {
			return;
		}
		mElementCongruenceGraph.addNode(nodeToAdd, null);
	}

	/**
	 * called from ElementCongruenceGraph.havoc on every node that was havocced.
	 * 
	 * @param node
	 */
	public void removeNode(NODE node) {
		assert !mIsFrozen;
		mNodes.remove(node);
	}

	public void addFunctionRaw(FUNCTION func) {
		assert !mIsFrozen;
		mFunctions.add(func);
		mFunctionEquivalenceGraph.addFunction(func);
	}

	public Set<FUNCTION> getAllFunctions() {
		return Collections.unmodifiableSet(mFunctions);
	}

	/**
	 * called from ElementCongruenceGraph.havoc on every node that was havocced.
	 * 
	 * @param node
	 */
	public void removeFunction(FUNCTION func) {
		assert !mIsFrozen;
		mFunctions.remove(func);
	}
	
	boolean allNodesAndEqgnMapAreConsistent() {
		return mElementCongruenceGraph.allNodesAndEqgnMapAreConsistent();
	}

	/**
	 * only called from mElementCongruenceGraph
	 * @param node
	 */
	public void addToAllNodes(NODE node) {
		mNodes.add(node);
		
	}

	public boolean isTop() {
		return mElementCongruenceGraph.isEmpty() && mFunctionEquivalenceGraph.isEmpty();
	}
}
