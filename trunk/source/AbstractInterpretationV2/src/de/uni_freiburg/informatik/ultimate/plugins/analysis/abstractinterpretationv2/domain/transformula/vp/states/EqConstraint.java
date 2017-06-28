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

public class EqConstraint<ACTION extends IIcfgTransition<IcfgLocation>, 
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {
	// implements IAbstractState<EqConstraint<ACTION, NODE, FUNCTION>,
	// IProgramVarOrConst> {

	private boolean mIsFrozen = false;

	CongruenceGraph<ACTION, NODE, FUNCTION> mElementCongruenceGraph;

	// UnionFind<FUNCTION> mFunctionEqualities;
	//
	// Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;

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
		// mFunctionEqualities = new UnionFind<>();
		mFunctionEquivalenceGraph = new ArrayEquivalenceGraph<>(this);
		// mFunctionDisequalities = new HashSet<>();

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
//		assert VPDomainHelpers.constraintFreeOfVars(Arrays.asList(node.getTerm().getFreeVars()), 
//				this, 
//				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) : 
//					"resulting constraint still has at least one of the to-be-projected vars";
	}

	public void havocFunction(FUNCTION func) {
		assert !mIsFrozen;

//		if (!mFunctions.stream().anyMatch(f -> f.dependsOn(func)) || isBottom()) {
		if (!mFunctions.contains(func) || isBottom()) {
//			assert VPDomainHelpers.constraintFreeOfVars(Arrays.asList(func.getTerm().getFreeVars()), this, 
//				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) : 
//					"resulting constraint still has at least one of the to-be-projected vars";
			return;
		}

		// havoc all dependent nodes
//		final Set<NODE> nodesWithFunc = mNodes.stream()
//				.filter(node -> ((node instanceof EqFunctionNode) && ((NODE) node).getFunction().dependsOn(func)))
//				.collect(Collectors.toSet());
//		nodesWithFunc.stream().forEach(node -> havoc(node));

		mFunctionEquivalenceGraph.havocFunction(func);
		assert !getAllFunctions().contains(func);
//		assert VPDomainHelpers.constraintFreeOfVars(Arrays.asList(func.getTerm().getFreeVars()), this, 
//				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) : 
//					"resulting constraint still has at least one of the to-be-projected vars";


		// // remove from function disequalities
		//// mFunctionDisequalities.removeIf(pair -> pair.contains(func));
		//
		// // remove from function equalities
		//// final UnionFind<FUNCTION> newFunctionEqualities = new
		// UnionFind<>();
		// final ArrayEquivalenceGraph<ACTION, NODE, FUNCTION>
		// newFunctionEqualities = new ArrayEquivalenceGraph<>();
		// // (union find has no remove -> has to be built anew)
		// for (Set<FUNCTION> eqc :
		// mFunctionEqualities.getAllEquivalenceClasses()) {
		// // look for an element that is not func --> everything but func will
		// be merged with it
		// Iterator<FUNCTION> eqcIt = eqc.iterator();
		// FUNCTION first = eqcIt.next();
		// while (first.dependsOn(func)) {
		// if (eqcIt.hasNext()) {
		// first = eqcIt.next();
		// } else {
		// // equivalence class has only elements that need to be havocced
		// for (FUNCTION el : eqc) {
		// newFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(el);
		// }
		// continue;
		// }
		// }
		// assert !first.dependsOn(func);
		//
		// for (FUNCTION el : eqc) {
		// newFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(el);
		// if (el.dependsOn(func)) {
		// // el is havocced --> don't merge its equivalence class
		// continue;
		// }
		// newFunctionEqualities.union(first, el);
		// }
		// }
		// mFunctionEqualities = newFunctionEqualities;

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

		for (TermVariable var : varsToProjectAway) {
			unfrozen.havoc(var);
//			if (var.getSort().isArraySort()) {
//				FUNCTION funcCorrespondingToVariable = getFunctionForTerm(var);
//				unfrozen.havocFunction(funcCorrespondingToVariable);
//			} else {
//				NODE nodeCorrespondingToVariable = getNodeForTerm(var);
//				unfrozen.havoc(nodeCorrespondingToVariable);
//			}
		}
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

	// /*
	// * **************** methods inherited from IAbstractState ****************
	// */
	//
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION>
	// addVariable(IProgramVarOrConst variable) {
	// // TODO Auto-generated method stub
	// return null;
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION>
	// removeVariable(IProgramVarOrConst variable) {
	// return removeVariables(Collections.singleton(variable));
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION>
	// addVariables(Collection<IProgramVarOrConst> variables) {
	// // TODO Auto-generated method stub
	// return null;
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION>
	// removeVariables(Collection<IProgramVarOrConst> variables) {
	// assert !mIsVersioned : "this constraint is not a 'predicate-style'
	// constraint, it should not be treated like an"
	// + " abstract state";
	// Set<TermVariable> termVariablesFromPvocs = variables.stream()
	// .map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());
	// return projectExistentially(termVariablesFromPvocs);
	// }
	//
	//
	// @Override
	// public boolean containsVariable(IProgramVarOrConst var) {
	// return getVariables().contains(var);
	// }
	//
	//
	// @Override
	// public Set<IProgramVarOrConst> getVariables() {
	// return mVariables;
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION> patch(EqConstraint<ACTION,
	// NODE, FUNCTION> dominator) {
	// EqConstraint<ACTION, NODE, FUNCTION> newConstraint =
	// this.removeVariables(dominator.getVariables());
	// return newConstraint.intersect(dominator);
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION>
	// intersect(EqConstraint<ACTION, NODE, FUNCTION> other) {
	// final List<EqConstraint<ACTION, NODE, FUNCTION>> constraints = new
	// ArrayList<>(2);
	// constraints.add(this);
	// constraints.add(other);
	// return mFactory.conjoin(constraints).flatten();
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION> union(EqConstraint<ACTION,
	// NODE, FUNCTION> other) {
	// final List<EqConstraint<ACTION, NODE, FUNCTION>> constraints = new
	// ArrayList<>(2);
	// constraints.add(this);
	// constraints.add(other);
	// return mFactory.getDisjunctiveConstraint(constraints).flatten();
	// }
	//
	//
	// @Override
	// public boolean isEmpty() {
	// return getVariables().isEmpty();
	// }
	//
	//
	// @Override
	// public boolean isEqualTo(EqConstraint<ACTION, NODE, FUNCTION> other) {
	// // TODO Auto-generated method stub
	// return false;
	// }
	//
	//
	// @Override
	// public SubsetResult isSubsetOf(EqConstraint<ACTION, NODE, FUNCTION>
	// other) {
	// // TODO Auto-generated method stub
	// return null;
	// }
	//
	//
	// @Override
	// public EqConstraint<ACTION, NODE, FUNCTION> compact() {
	// // TODO Auto-generated method stub
	// return null;
	// }
	//
	//
	// @Override
	// public Term getTerm(Script script) {
	// // TODO Auto-generated method stub
	// return null;
	// }
	//
	//
	// @Override
	// public String toLogString() {
	// // TODO Auto-generated method stub
	// return null;
	// }

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

		//// final UnionFind<FUNCTION> newFunctionUF = new UnionFind<>();
		// final ArrayEquivalenceGraph<ACTION, NODE, FUNCTION> newFunctionUF =
		//// new ArrayEquivalenceGraph<>();
		//// for (Entry<FUNCTION, FUNCTION> fEq :
		//// getSupportingFunctionEqualities()) {
		// for (Set<FUNCTION> eqc :
		//// mFunctionEquivalenceGraph.getAllEquivalenceClasses()) {
		// FUNCTION first =
		//// newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
		// eqc.iterator().next().renameVariables(substitutionMapping));
		// for (FUNCTION f : eqc) {
		// FUNCTION renamedF =
		//// newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
		// f.renameVariables(substitutionMapping));
		// newFunctionUF.union(first, renamedF);
		//// FUNCTION renamedF1 =
		//// newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
		//// fEq.getKey().renameVariables(substitutionMapping));
		//// FUNCTION renamedF2 =
		//// newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
		//// fEq.getKey().renameVariables(substitutionMapping));
		//// newFunctionUF.union(renamedF1, renamedF2);
		// }
		// }
		// mFunctionEquivalenceGraph = newFunctionUF;
		mFunctionEquivalenceGraph.renameVariables(substitutionMapping);

		// Set<VPDomainSymmetricPair<FUNCTION>> newFunctionDisequalites = new
		// HashSet<>();
		// for (VPDomainSymmetricPair<FUNCTION> fDeq : mFunctionDisequalities) {
		// newFunctionDisequalites.add(new VPDomainSymmetricPair<FUNCTION>(
		// fDeq.getFirst().renameVariables(substitutionMapping),
		// fDeq.getSecond().renameVariables(substitutionMapping)));
		// }
		// mFunctionDisequalities = newFunctionDisequalites;
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

		// if (node.isLiteral()) {
		// // towards symbolic treatment of literal disequalities between
		// literals
		// result.addAll(mNodes.stream()
		// .filter(n -> (!n.equals(node) && n.isLiteral())) // keep only
		// literals unequal to node
		// .map(n -> mElementCongruenceGraph.find(node)) // take their
		// representatives
		// .filter(n -> n != null)
		// .collect(Collectors.toSet()));
		// } else {
		final NODE nodeRep = mElementCongruenceGraph.find(node);
		for (VPDomainSymmetricPair<NODE> deq : mElementCongruenceGraph.getDisequalities()) {
			if (deq.contains(nodeRep)) {
				result.add(deq.getOther(nodeRep));
			}
		}
		// }
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

	/**
	 * (expensive)
	 * @return all disequalities (as symmetric pairs) that hold in this state, i.e., not only those over representatives
	 */
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
//		mNodes.add(nodeToAdd); // done by mElementCongruenceGraph (also for child nodes)
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
//		mFunctions.removeIf(f -> f.dependsOn(func));
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
