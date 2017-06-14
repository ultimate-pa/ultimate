package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class EqConstraint<
					ACTION extends IIcfgTransition<IcfgLocation>, 
					NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
					FUNCTION extends IEqFunctionIdentifier<FUNCTION>>  {
//	implements IAbstractState<EqConstraint<ACTION, NODE, FUNCTION>, IProgramVarOrConst>  {

	private boolean mIsFrozen = false;

	CongruenceGraph<NODE, FUNCTION> mElementCongruenceGraph;

	UnionFind<FUNCTION> mFunctionEqualities;
	
	Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;

	private EqConstraintFactory<ACTION, NODE, FUNCTION> mFactory;

	private boolean mIsVersioned;

	private Set<IProgramVar> mVariables;
	private Set<IProgramVarOrConst> mPvocs;

	/**
	 * All (element) nodes that this constraint currently knows about
	 */
	private Set<NODE> mNodes = new HashSet<>();
	
	/**
	 * Creates an empty constraint (i.e. it does not constrain anything, is equivalent to "true")
	 * 
	 * @param factory
	 */
	public EqConstraint(EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		mFactory = factory;
		
		mElementCongruenceGraph = new CongruenceGraph<>();
		mFunctionEqualities = new UnionFind<>();
		mFunctionDisequalities = new HashSet<>();

	}

	/**
	 * copy constructor
	 * @param constraint
	 */
	public EqConstraint(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		mFactory = constraint.mFactory;
		mElementCongruenceGraph = new CongruenceGraph<>(constraint.mElementCongruenceGraph);

		// copy the union find containing array equalities
		mFunctionEqualities = new UnionFind<>();
		for (FUNCTION rep : constraint.mFunctionEqualities.getAllRepresentatives()) {
			mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(rep);
			for (FUNCTION mem : constraint.mFunctionEqualities.getEquivalenceClassMembers(rep)) {
				mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(mem);
				mFunctionEqualities.union(mem, rep);
			}
		}

		mFunctionDisequalities = new HashSet<>(constraint.mFunctionDisequalities);
	}

	/**
	 * 
	 * @param node1
	 * @param node2
	 * @return The merge history, i.e., all pairs of former representatives that have been merged by this merge 
	 *    operation
	 */
	public HashRelation<NODE, NODE> merge(NODE node1, NODE node2) {
		return mElementCongruenceGraph.merge(node1, node2);
	}

	public void havoc(NODE node) {
		assert !mIsFrozen;
		if (isBottom()) {
			return;
		}
		mElementCongruenceGraph.havoc(node);
	}
	
	public void havocFunction(FUNCTION func) {
		assert !mIsFrozen;
		
	}
	
	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
		mElementCongruenceGraph.freeze();
		mFunctionDisequalities = Collections.unmodifiableSet(mFunctionDisequalities);
	}


	public boolean isBottom() {
		return false;
	}


	public Set<NODE> getAllNodes() {
		// TODO Auto-generated method stub
		return null;
	}


//	public void addNodes(Collection<NODE> allNodes) {
//		mElementCongruenceGraph.addNodes(allNodes);
//	}


	public HashRelation<NODE, NODE> getSupportingElementEqualities() {
		return mElementCongruenceGraph.getSupportingEqualities();
	}


	public Set<VPDomainSymmetricPair<NODE>> getElementDisequalities() {
		return mElementCongruenceGraph.getDisequalities();
	}


	/**
	 * "Raw" means here that the disequality is not yet normalized such that it only speaks about equivalence 
	 * representatives.
	 * 
	 * @param first
	 * @param second
	 */
	public void addRawDisequality(NODE first, NODE second) {
		assert !mIsFrozen;
		mElementCongruenceGraph.addDisequality(
				mElementCongruenceGraph.find(first), 
				mElementCongruenceGraph.find(second));
	}


	public HashRelation<FUNCTION, FUNCTION> getSupportingFunctionEqualities() {
		/*
		 * plan: for each equivalence class, iterate over the elements and report an equality for each two consecutive
		 *  elements
		 */
		HashRelation<FUNCTION, FUNCTION> result = new HashRelation<>();
		for (Set<FUNCTION> eqClass : mFunctionEqualities.getAllEquivalenceClasses()) {
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


	public void addFunctionEquality(FUNCTION key, FUNCTION value) {
		mFunctionEqualities.union(mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(key),
				mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(value));
		
		// TODO: adding a function equality can have consequences for the elements --> implement
	}


	public  Set<VPDomainSymmetricPair<FUNCTION>> getFunctionDisequalites() {
		return mFunctionDisequalities;
	}


	public void addFunctionDisequality(FUNCTION first, FUNCTION second) {
		assert false : "TODO: work with UF-representatives..";//TODO
		mFunctionDisequalities.add(new VPDomainSymmetricPair<FUNCTION>(first, second));
	}


	public boolean checkForContradiction() {
		if (mElementCongruenceGraph.checkContradiction()) {
			return true;
		}
		for (VPDomainSymmetricPair<FUNCTION> fDeq : mFunctionDisequalities) {
			if (mFunctionEqualities.find(fDeq.getFirst()).equals(mFunctionEqualities.find(fDeq.getSecond()))) {
				return true;
			}
		}
		return false;
	}


	public boolean isFrozen() {
		return mIsFrozen;
	}
	
	/**
	 * 
	 * 
	 * TODO: should we also remove the nodes that we project, here??
	 * @param varsToProjectAway
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> projectExistentially(Set<TermVariable> varsToProjectAway) {
		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = mFactory.unfreeze(this);

		for (TermVariable var : varsToProjectAway) {
			NODE nodeCorrespondingToVariable = getNodeForTerm(var);
			unfrozen.havoc(nodeCorrespondingToVariable);
		}
		unfrozen.freeze();
		return unfrozen;
	}

	private NODE getNodeForTerm(TermVariable var) {
		// TODO Auto-generated method stub
		return null;
	}

//	/*
//	 * **************** methods inherited from IAbstractState ****************
//	 */
//
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> addVariable(IProgramVarOrConst variable) {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> removeVariable(IProgramVarOrConst variable) {
//		return removeVariables(Collections.singleton(variable));
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> addVariables(Collection<IProgramVarOrConst> variables) {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> removeVariables(Collection<IProgramVarOrConst> variables) {
//		assert !mIsVersioned : "this constraint is not a 'predicate-style' constraint, it should not be treated like an"
//				+ " abstract state";
//		Set<TermVariable> termVariablesFromPvocs = variables.stream()
//				.map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());
//		return projectExistentially(termVariablesFromPvocs);
//	}
//
//
//	@Override
//	public boolean containsVariable(IProgramVarOrConst var) {
//		return getVariables().contains(var);
//	}
//
//
//	@Override
//	public Set<IProgramVarOrConst> getVariables() {
//		return mVariables;
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> patch(EqConstraint<ACTION, NODE, FUNCTION> dominator) {
//		EqConstraint<ACTION, NODE, FUNCTION> newConstraint = this.removeVariables(dominator.getVariables());
//		return newConstraint.intersect(dominator);
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> intersect(EqConstraint<ACTION, NODE, FUNCTION> other) {
//		final List<EqConstraint<ACTION, NODE, FUNCTION>> constraints = new ArrayList<>(2);
//		constraints.add(this);
//		constraints.add(other);
//		return mFactory.conjoin(constraints).flatten();
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> union(EqConstraint<ACTION, NODE, FUNCTION> other) {
//		final List<EqConstraint<ACTION, NODE, FUNCTION>> constraints = new ArrayList<>(2);
//		constraints.add(this);
//		constraints.add(other);
//		return mFactory.getDisjunctiveConstraint(constraints).flatten();
//	}
//
//
//	@Override
//	public boolean isEmpty() {
//		return getVariables().isEmpty();
//	}
//
//
//	@Override
//	public boolean isEqualTo(EqConstraint<ACTION, NODE, FUNCTION> other) {
//		// TODO Auto-generated method stub
//		return false;
//	}
//
//
//	@Override
//	public SubsetResult isSubsetOf(EqConstraint<ACTION, NODE, FUNCTION> other) {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	@Override
//	public EqConstraint<ACTION, NODE, FUNCTION> compact() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	@Override
//	public Term getTerm(Script script) {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	@Override
//	public String toLogString() {
//		// TODO Auto-generated method stub
//		return null;
//	}


	public void renameVariables(Map<Term, Term> substitutionMapping) {
		assert !mIsFrozen;
		
		mElementCongruenceGraph.renameVariables(substitutionMapping);
		
		final UnionFind<FUNCTION> newFunctionUF = new UnionFind<>();
		for (Entry<FUNCTION, FUNCTION> fEq : getSupportingFunctionEqualities()) {
			FUNCTION renamedF1 = newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
					fEq.getKey().renameVariables(substitutionMapping));
			FUNCTION renamedF2 = newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
					fEq.getKey().renameVariables(substitutionMapping));
			newFunctionUF.union(renamedF1, renamedF2);
		}
		mFunctionEqualities = newFunctionUF;
		
		Set<VPDomainSymmetricPair<FUNCTION>> newFunctionDisequalites = new HashSet<>();
		for (VPDomainSymmetricPair<FUNCTION> fDeq : mFunctionDisequalities) {
			newFunctionDisequalites.add(new VPDomainSymmetricPair<FUNCTION>(
					fDeq.getFirst().renameVariables(substitutionMapping), 
					fDeq.getSecond().renameVariables(substitutionMapping)));
		}
		mFunctionDisequalities = newFunctionDisequalites;
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
		final VPDomainSymmetricPair<NODE> representativePair = new VPDomainSymmetricPair<>(
				find1, find2);
		return mElementCongruenceGraph.getDisequalities().contains(representativePair);
	}

	/**
	 * Returns all the equivalence representatives that the given node is unequal to in this constraint.
	 */
	public Set<NODE> getDisequalities(NODE node) {
		final Set<NODE> result = new HashSet<>();
		for (VPDomainSymmetricPair<NODE> deq : mElementCongruenceGraph.getDisequalities()) {
			if (deq.contains(node)) {
				result.add(deq.getOther(node));
			}
		}
		return result;
	}

	
	public Term getTerm(Script script) {
		final List<Term> elementEqualities = getSupportingElementEqualities().entrySet().stream()
			.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm())).collect(Collectors.toList());
		final List<Term> elementDisequalities = getElementDisequalities().stream()
				.map(pair -> script.term("distinct", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionEqualities = getSupportingFunctionEqualities().entrySet().stream()
			.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm())).collect(Collectors.toList());
		final List<Term> functionDisequalities = getFunctionDisequalites().stream()
				.map(pair -> script.term("distinct", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
				.collect(Collectors.toList());
		
		final List<Term> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(elementEqualities);
		allConjuncts.addAll(elementDisequalities);
		allConjuncts.addAll(functionEqualities);
		allConjuncts.addAll(functionDisequalities);
		
		if (allConjuncts.isEmpty()) {
			return script.term("true");
		}

		return script.term("and", allConjuncts.toArray(new Term[allConjuncts.size()]));
	}

	public boolean areEqual(FUNCTION node1, FUNCTION node2) {
		return mFunctionEqualities.find(node1).equals(mFunctionEqualities.find(node2));
	}
	
	public boolean areUnequal(FUNCTION node1, FUNCTION node2) {
		final FUNCTION rep1 = mFunctionEqualities.find(node1);
		final FUNCTION rep2 = mFunctionEqualities.find(node2);
		return mFunctionDisequalities.contains(new VPDomainSymmetricPair<FUNCTION>(rep1, rep2));
	}

	public Set<IProgramVar> getVariables() {
		return mVariables;
	}
	
	public Set<IProgramVarOrConst> getPvocs() {
		return mPvocs;
	}

	/**
	 * all equalities that hold in this constraint
	 * (transitive, symmetric closure)
	 * @return
	 */
	public Set<VPDomainSymmetricPair<NODE>> getAllElementEqualities() {
		Set<VPDomainSymmetricPair<NODE>> result = new HashSet<>();
		final List<NODE> allNodes = new ArrayList<>(getAllNodes());
		for (int i = 0; i < allNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				if (areEqual(allNodes.get(i), allNodes.get(i))) {
					result.add(new VPDomainSymmetricPair<NODE>(allNodes.get(i), allNodes.get(j)));
				}
			}
		}
		return result;
	}
	
	public Set<VPDomainSymmetricPair<NODE>> getAllElementDisequalities() {
		Set<VPDomainSymmetricPair<NODE>> result = new HashSet<>();
		final List<NODE> allNodes = new ArrayList<>(getAllNodes());
		for (int i = 0; i < allNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				if (areUnequal(allNodes.get(i), allNodes.get(i))) {
					result.add(new VPDomainSymmetricPair<NODE>(allNodes.get(i), allNodes.get(j)));
				}
			}
		}
		return result;
	}

	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionEqualities() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionDisequalities() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public String toString() {
		// (adapted from getTerm())
		final List<String> elementEqualities = getSupportingElementEqualities().entrySet().stream()
			.map(en -> String.format("(%s = %s)", en.getKey().getTerm(), en.getValue().getTerm())).collect(Collectors.toList());
		final List<String> elementDisequalities = getElementDisequalities().stream()
				.map(pair -> String.format("(%s != %s)", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
				.collect(Collectors.toList());
		final List<String> functionEqualities = getSupportingFunctionEqualities().entrySet().stream()
			.map(en -> String.format("(%s = %s)", en.getKey().getTerm(), en.getValue().getTerm())).collect(Collectors.toList());
		final List<String> functionDisequalities = getFunctionDisequalites().stream()
				.map(pair -> String.format("(%s != %s)", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
				.collect(Collectors.toList());
		
		final List<String> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(elementEqualities);
		allConjuncts.addAll(elementDisequalities);
		allConjuncts.addAll(functionEqualities);
		allConjuncts.addAll(functionDisequalities);
		
		if (allConjuncts.isEmpty()) {
			return "Top";
		}
		
		final StringBuilder sb = new StringBuilder();
		for (String s : allConjuncts) {
			sb.append(s);
		}


		return sb.toString();
	}
	
	public boolean hasNode(NODE node) {
		return mNodes.contains(node);
	}

	/**
	 * Add a node to this constraint. Does not do any propagations that might be a consequence of adding this node.
	 * @param nodeToAdd
	 */
	public void addNodeRaw(NODE nodeToAdd) {
		if (hasNode(nodeToAdd)) {
			return;
		}
		mNodes.add(nodeToAdd);
		mElementCongruenceGraph.addNode(nodeToAdd, null);
	}
	
}
