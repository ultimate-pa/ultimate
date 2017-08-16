package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

public class EqConstraintNew<ACTION extends IIcfgTransition<IcfgLocation>,
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	CongruenceClosure<NODE, FUNCTION> mPartialArrangement;

	private Set<IProgramVar> mVariables;
	private Set<IProgramVarOrConst> mPvocs;
	private boolean mIsFrozen;

	WeakEquivalenceGraph mWeakEquivalenceGraph;

//	HashRelation3 mWeakEquivalences

	///////////////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////////////

	/**
	 * Creates an empty constraint (i.e. it does not constrain anything, is
	 * equivalent to "true")
	 *
	 * @param factory
	 */
	public EqConstraintNew(final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
	}

	/**
	 * copy constructor
	 *
	 * @param constraint
	 */
	public EqConstraintNew(final EqConstraintNew<ACTION, NODE, FUNCTION> constraint) {
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @return The merge history, i.e., all pairs of former representatives that
	 *         have been merged by this merge operation
	 */
	public HashRelation<NODE, NODE> merge(final NODE node1, final NODE node2) {
		return null;
	}

	public void havoc(final NODE node) {
	}

	public void havocFunction(final FUNCTION func) {
	}

	public void freeze() {
	}

	public boolean isBottom() {
		return false;
	}

	public Set<NODE> getAllNodes() {
		return null;
	}

	public HashRelation<NODE, NODE> getSupportingElementEqualities() {
		return null;
	}

	public Set<VPDomainSymmetricPair<NODE>> getElementDisequalities() {
		return null;
	}

	/**
	 * "Raw" means here that the disequality is not yet normalized such that it
	 * only speaks about equivalence representatives.
	 *
	 * @param first
	 * @param second
	 */
	public void addRawDisequality(final NODE first, final NODE second) {
	}

	public void addFunctionEqualityRaw(final FUNCTION func1, final FUNCTION func2) {
	}

	public void addFunctionDisequality(final FUNCTION first, final FUNCTION second) {
	}

	public boolean checkForContradiction() {
		assert false;
		return false;
	}

	public boolean isFrozen() {
		assert false;
		return false;
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
	public EqConstraint<ACTION, NODE, FUNCTION> projectExistentially(final Set<TermVariable> varsToProjectAway) {
//		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = mFactory.unfreeze(this);
//
//
//		varsToProjectAway.forEach(var -> unfrozen.havoc(var));
//
////		for (TermVariable var : varsToProjectAway) {
////			unfrozen.havoc(var);
////		}
//		unfrozen.freeze();
//		assert VPDomainHelpers.constraintFreeOfVars(varsToProjectAway, unfrozen,
//				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) :
//					"resulting constraint still has at least one of the to-be-projected vars";
//
//		return unfrozen;
		return null;
	}


	private void havoc(final TermVariable var) {
	}

	private FUNCTION getFunctionForTerm(final Term var) {
		return null;
	}

	private NODE getNodeForTerm(final Term var) {
		return null;
	}

	public void renameVariables(final Map<Term, Term> substitutionMapping) {
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @return true iff this constraint says "node1 and node2 must be equal"
	 */
	public boolean areEqual(final NODE node1, final NODE node2) {
		assert false;
		return false;
	}

	public HashRelation<FUNCTION, List<NODE>> getCCChild(final NODE representative1) {
		return null;
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @return true iff this constraint says "node1 and node2 must be unequal"
	 */
	public boolean areUnequal(final NODE node1, final NODE node2) {
		assert false;
		return false;
	}

	/**
	 * Returns all the equivalence representatives that the given node is
	 * unequal to in this constraint.
	 */
	public Set<NODE> getDisequalities(final NODE node) {
		return null;
	}

	public Term getTerm(final Script script) {
//		assert mIsFrozen : "not yet frozen, term may not be final..";
//		if (mTerm != null) {
//			return mTerm;
//		}
//		final List<Term> elementEqualities = getSupportingElementEqualities().entrySet().stream()
//				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
//				.collect(Collectors.toList());
//		final List<Term> elementDisequalities = getElementDisequalities().stream()
//				.map(pair -> script.term("distinct", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
//				.collect(Collectors.toList());
//		final List<Term> functionEqualities = getSupportingFunctionEqualities().entrySet().stream()
//				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
//				.collect(Collectors.toList());
//		final List<Term> functionDisequalities = getFunctionDisequalites().stream()
//				.map(pair -> script.term("distinct", pair.getFirst().getTerm(), pair.getSecond().getTerm()))
//				.collect(Collectors.toList());
//
//		final List<Term> allConjuncts = new ArrayList<>();
//		allConjuncts.addAll(elementEqualities);
//		allConjuncts.addAll(elementDisequalities);
//		allConjuncts.addAll(functionEqualities);
//		allConjuncts.addAll(functionDisequalities);
//
//		final Term result= Util.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
//		if (mIsFrozen) {
//			mTerm = result;
//		}
//		return result;
		return null;
	}

	public boolean areEqual(final FUNCTION func1, final FUNCTION func2) {
		assert false;
		return false;
	}

	public boolean areUnequal(final FUNCTION func1, final FUNCTION func2) {
		assert false;
		return false;
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
	public Set<IProgramVar> getVariables(final IIcfgSymbolTable symbolTable) {
		if (mVariables == null) {
			final Set<TermVariable> allTvs = new HashSet<>();
			mPartialArrangement.getAllElements().stream()
				.forEach(node -> allTvs.addAll(Arrays.asList(node.getTerm().getFreeVars())));

			mPartialArrangement.getAllFunctions().stream()
				.forEach(func -> allTvs.addAll(Arrays.asList(func.getTerm().getFreeVars())));

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
	public Set<IProgramVarOrConst> getPvocs(final IIcfgSymbolTable symbolTable) {
		assert mIsFrozen;
		if (mPvocs == null) {
			mPvocs = new HashSet<>();
			mPvocs.addAll(getVariables(symbolTable));

			final Set<ApplicationTerm> constants = new HashSet<>();
			mPartialArrangement.getAllElements().stream()
					.forEach(node -> constants.addAll(new ConstantFinder().findConstants(node.getTerm(), false)));
			// TODO do we need to find literals here, too?? (i.e. ConstantTerms)

			mPartialArrangement.getAllFunctions().stream()
					.forEach(func -> constants.addAll(new ConstantFinder().findConstants(func.getTerm(), false)));

			mPvocs.addAll(constants.stream().map(c -> symbolTable.getProgramConst(c)).collect(Collectors.toSet()));
		}
		return mPvocs;
	}

//	/**
//	 * all equalities that hold in this constraint (transitive, symmetric
//	 * closure)
//	 *
//	 * @return
//	 */
//	public Set<VPDomainSymmetricPair<NODE>> getAllElementEqualities() {
//		final Set<VPDomainSymmetricPair<NODE>> result = new HashSet<>();
//		final List<NODE> allNodes = new ArrayList<>(getAllNodes());
//		for (int i = 0; i < allNodes.size(); i++) {
//			for (int j = 0; j < i; j++) {
//				if (areEqual(allNodes.get(i), allNodes.get(j))) {
//					result.add(new VPDomainSymmetricPair<NODE>(allNodes.get(i), allNodes.get(j)));
//				}
//			}
//		}
//		return result;
//	}
//
//	/**
//	 * (expensive)
//	 * @return all disequalities (as symmetric pairs) that hold in this state, i.e., not only those over representatives
//	 */
//	public Set<VPDomainSymmetricPair<NODE>> getAllElementDisequalities() {
//		final Set<VPDomainSymmetricPair<NODE>> result = new HashSet<>();
//		final List<NODE> allNodes = new ArrayList<>(getAllNodes());
//		for (int i = 0; i < allNodes.size(); i++) {
//			for (int j = 0; j < i; j++) {
//				if (areUnequal(allNodes.get(i), allNodes.get(j))) {
//					result.add(new VPDomainSymmetricPair<NODE>(allNodes.get(i), allNodes.get(j)));
//				}
//			}
//		}
//		return result;
//	}

//	/**
//	 * retrieves all equalities between functions that we know hold
//	 * more precise:
//	 *  - is transitively closed
//	 *  - symmetrically closed through use of VPDomainSymmetricPair
//	 *  - does not explicitly account for reflexivity
//	 * @return
//	 */
//	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionEqualities() {
//		return mPartialArrangement.getFu
//	}

//	/**
//	 * analogue to getAllFunctionEqualities, i.e. _all_ disequalities, not only the disequalities over representatives
//	 * @return
//	 */
//	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionDisequalities() {
////		return mPartialArrangement.getFunctionDisequalities();
//		return null;
//	}

	@Override
	public String toString() {

		final List<String> allPartitionsAndRepresentativeDisequalities = new ArrayList<>();

		String sep = "";
		final StringBuilder sb = new StringBuilder();
		for (final String s : allPartitionsAndRepresentativeDisequalities) {
			sb.append(sep);
			sep = "\n";
			sb.append(s);
		}

		return sb.toString();

	}

	public boolean hasNode(final NODE node) {
		return mPartialArrangement.getAllElements().contains(node);
	}

//	/**
//	 * Add a node to this constraint. Does not do any propagations that might be
//	 * a consequence of adding this node.
//	 *
//	 * @param nodeToAdd
//	 */
//	public void addNodeRaw(final NODE nodeToAdd) {
//		assert !mIsFrozen;
//		if (hasNode(nodeToAdd)) {
//			return;
//		}
//		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(nodeToAdd);
//	}
//
//	public void addFunctionRaw(final FUNCTION func) {
//		assert !mIsFrozen;
//		mFunctions.add(func);
//		mFunctionEquivalenceGraph.addFunction(func);
//	}

	public Set<FUNCTION> getAllFunctions() {
		return mPartialArrangement.getAllFunctions();
	}

	public boolean isTop() {
		assert false;
		return false;
	}

	public EqConstraintNew<ACTION, NODE, FUNCTION> join(final EqConstraintNew<ACTION, NODE, FUNCTION> other) {
		final CongruenceClosure<NODE, FUNCTION> newPartialArrangement = this.mPartialArrangement.join(
				other.mPartialArrangement);
		final WeakEquivalenceGraph newWEGraph = mWeakEquivalenceGraph.join(other.mWeakEquivalenceGraph);
		return null; // factory.getEqConstraint(newPartial..)
	}


	class WeakEquivalenceGraph//<ACTION extends IIcfgTransition<IcfgLocation>,
//	NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
//	FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {
	{

		HashRelation3<FUNCTION, FUNCTION, CongruenceClosure<NODE, FUNCTION>> mWeakEquivalenceEdges =
				new HashRelation3<>();

		WeakEquivalenceGraph join(final WeakEquivalenceGraph other) {
			return null;
		}

	}
}
//class WeakEquivalenceEdge<//ACTION extends IIcfgTransition<IcfgLocation>,
//		NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
//		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {
//
//	FUNCTION mFunction1;
//	FUNCTION mFunction2;
////	List<ThreeValuedEquivalenceRelation<NODE>> mStoreConstraints;
//	List<CongruenceClosure<NODE, FUNCTION>> mStoreConstraints;
//
//
//
//}
