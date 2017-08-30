package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

public class WeqCongruenceClosure<ACTION extends IIcfgTransition<IcfgLocation>,
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>>
		extends CongruenceClosure<NODE, FUNCTION> {

	private final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> mWeakEquivalenceGraph;

	public WeqCongruenceClosure(final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		super();
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, factory);
	}

	public WeqCongruenceClosure(final boolean isInconsistent) {
		super(true);
		if (!isInconsistent) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mWeakEquivalenceGraph = null;
	}



	/**
		 *
		 *
		 * @param original
		 */
		public WeqCongruenceClosure(final CongruenceClosure<NODE, FUNCTION> original,
				final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weqGraph) {
			super(original);
			if (original.isInconsistent()) {
				throw new IllegalArgumentException("use other constructor!");
			}
	//		mWeakEquivalenceGraph = weqGraph;
			// we need a fresh instance here, because we cannot set the link in the weq graph to the right cc instance..
			mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, weqGraph);
		}


	/**
		 * copy constructor
		 *
		 * @param original
		 */
		public WeqCongruenceClosure(final WeqCongruenceClosure<ACTION, NODE, FUNCTION> original) {
	//			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weqGraph) {
			super(original);
	//		assert original.mWeakEquivalenceGraph == weqGraph : "?";
			mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, original.mWeakEquivalenceGraph);
		}


	public Term getTerm(final Script script) {
		final List<Term> allConjuncts =  new ArrayList<>();
		allConjuncts.addAll(EqConstraint.partialArrangementToCube(script, this));

		final List<Term> weakEqConstraints = mWeakEquivalenceGraph.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result= SmtUtils.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
			return result;
	}

	@Override
	protected CongruenceClosure<NODE, FUNCTION> alignElementsAndFunctions(
			final CongruenceClosure<NODE, FUNCTION> otherCC) {
		if (!(otherCC instanceof WeqCongruenceClosure)) {
			return super.alignElementsAndFunctions(otherCC);
		}
		final WeqCongruenceClosure<ACTION, NODE, FUNCTION> other =
				(WeqCongruenceClosure<ACTION, NODE, FUNCTION>) otherCC;

		final WeqCongruenceClosure<ACTION, NODE, FUNCTION> result = new WeqCongruenceClosure<>(this);
		assert result.sanityCheck();

		other.getAllElements().stream().forEach(elem -> result.addElement(elem));
		other.getAllFunctions().stream().forEach(func -> result.mFunctionTVER.addElement(func));

		assert result.sanityCheck();
		return result;
	}

	public void renameVariables(final Map<Term, Term> substitutionMapping) {
		transformElementsAndFunctions(
				node -> node.renameVariables(substitutionMapping),
				function -> function.renameVariables(substitutionMapping));
		mWeakEquivalenceGraph.renameVariables(substitutionMapping);
	}

	public void reportWeakEquivalence(final FUNCTION array1, final FUNCTION array2, final List<NODE> storeIndex) {
		for (final NODE storeIndexNode : storeIndex) {
			getRepresentativeAndAddElementIfNeeded(storeIndexNode);
		}
		getRepresentativeAndAddFunctionIfNeeded(array1);
		getRepresentativeAndAddFunctionIfNeeded(array2);
		mWeakEquivalenceGraph.reportWeakEquivalence(array1, array2, storeIndex);
	}


	@Override
	protected boolean reportEqualityRec(final NODE node1, final NODE node2) {
		boolean madeChanges = false;

		madeChanges |= super.reportEqualityRec(node1, node2);

		if (!madeChanges) {
			return false;
		}

		// congruence closure-like checks for weak equivalence:
		final Set<Doubleton<NODE>> propagatedEqualitiesFromWeqEdges =
				mWeakEquivalenceGraph.getWeakCongruencePropagations(node1, node2);
		for (final Doubleton<NODE> eq : propagatedEqualitiesFromWeqEdges) {
			madeChanges |= this.reportEquality(eq.getOneElement(), eq.getOtherElement());
		}

		// should we do this for every equality or only the ones reported on EqConstraint level??
		mWeakEquivalenceGraph.reportChangeInGroundPartialArrangement(
				(final CongruenceClosure<NODE, FUNCTION> cc) -> cc.reportEquality(node1, node2));
		while (mWeakEquivalenceGraph.hasArrayEqualities()) {
			final Entry<FUNCTION, FUNCTION> aeq = mWeakEquivalenceGraph.pollArrayEquality();
			reportFunctionEquality(aeq.getKey(), aeq.getValue());
		}

		return madeChanges;
	}

	@Override
	public boolean isTautological() {
		return super.isTautological() && mWeakEquivalenceGraph.isEmpty();
	}



	@Override
	public boolean isStrongerThan(final CongruenceClosure<NODE, FUNCTION> other) {
		if (!(other instanceof WeqCongruenceClosure<?, ?, ?>)) {
			throw new IllegalArgumentException();
		}
		if (!super.isStrongerThan(other)) {
			return false;
		}

		final WeqCongruenceClosure<ACTION, NODE, FUNCTION> otherWeqCc =
				(WeqCongruenceClosure<ACTION, NODE, FUNCTION>) other;

		if (!mWeakEquivalenceGraph.isStrongerThan(otherWeqCc.mWeakEquivalenceGraph)) {
			return false;
		}
		return true;
	}



	@Override
	public boolean removeFunction(final FUNCTION func) {
		if (!hasFunction(func)) {
			return false;
		}
		final CongruenceClosure<NODE,FUNCTION> copy = new CongruenceClosure<>(this);
		copy.removeFunction(func);
		mWeakEquivalenceGraph.projectFunction(func, copy);
		assert projectedFunctionIsGoneFromWeqGraph(func, mWeakEquivalenceGraph);

		/*
		 * the following code is c/p'ed from super.removeFunction, with one marked exception (see below)
		 */

		// remove all elements that depend on the function
		final Set<NODE> funcAppsWithFuncCopy = new HashSet<>(mFunctionToFuncApps.getImage(func));
		for (final NODE funcApp : funcAppsWithFuncCopy) {
			// change from original: (added second argument)
			removeElement(funcApp, copy);
			assert projectedFunctionIsGoneFromWeqGraph(func, mWeakEquivalenceGraph);
		}

		// remove from the function equivalence relation
		mFunctionTVER.removeElement(func);

		mFunctionToRepresentativeToCcPars.remove(func);
		mFunctionToRepresentativeToCcChildren.remove(func);
		mFunctionToFuncApps.removeDomainElement(func);
		assert projectedFunctionIsGoneFromWeqGraph(func, mWeakEquivalenceGraph);
		assert sanityCheck();
		return true;
	}




	@Override
	public boolean removeElement(final NODE elem) {
		if (!hasElement(elem)) {
			return false;
		}
		final CongruenceClosure<NODE,FUNCTION> copy = new CongruenceClosure<>(this);
		copy.removeElement(elem);
		return removeElement(elem, copy);
	}

	private boolean projectedFunctionIsGoneFromWeqGraph(final FUNCTION func,
			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weakEquivalenceGraph) {
		for (final Entry<Doubleton<FUNCTION>,
				WeakEquivalenceGraph<ACTION, NODE, FUNCTION>.WeakEquivalenceEdgeLabel> edge :
					weakEquivalenceGraph.getEdges().entrySet()) {
			if (edge.getValue().getAppearingFunctions().contains(func)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public boolean removeElement(final NODE elem, final CongruenceClosure<NODE, FUNCTION> copy) {
		if (!hasElement(elem)) {
			return false;
		}
		mWeakEquivalenceGraph.projectElement(elem, copy);

		super.purgeElem(elem);

		/*
		 * recursive call: if an element is removed, all the function applications that have it as an argument are
		 * removed, too
		 */
		for (final NODE parent : new HashSet<>(mElementToParents.getImage(elem))) {
			removeElement(parent, copy); // change
		}
		mElementToParents.removeDomainElement(elem);
		mElementToParents.removeRangeElement(elem);

		assert elementIsFullyRemoved(elem);
		return true;


	}


	@Override
	protected void registerNewElement(final NODE elem) {
		super.registerNewElement(elem);

		if (!elem.isFunctionApplication()) {
			// nothing to do
			return;
		}

		/*
		 * As the new element is a function application, we might be able to infer equalities for it through weak
		 * equivalence.
		 */
		for (final Entry<FUNCTION, WeakEquivalenceGraph<ACTION, NODE, FUNCTION>.WeakEquivalenceEdgeLabel> edge :
				mWeakEquivalenceGraph.getAdjacentWeqEdges(elem.getAppliedFunction()).entrySet()) {
			Set<NODE> candidateSet = null;

			/*
			 * obtain "candidate elements", i.e, elements that might be equivalent to elem insofar their arguments are
			 * equal and their applied function is weakly equivalent to elem's applied function
			 */
			for (int i = 0; i < elem.getArguments().size(); i++) {
				final NODE argRep = mElementTVER.getRepresentative(elem.getArguments().get(i));
				final Set<NODE> newCandidates = getCcParsForArgumentPosition(edge.getKey(), argRep, i);
				if (candidateSet == null) {
					candidateSet = new HashSet<>(newCandidates);
				} else {
					candidateSet.retainAll(newCandidates);
				}
			}

			for (final NODE c : candidateSet) {
				if (c == elem) {
					continue;
				}

				/*
				 * check if the weak equivalence is strong enough to allow propagation of elem = c
				 * (elem and c have the form  a[...], b[...], where we have a weak equivalence edge (current edge)
				 *  between a and c)
				 */
				if (edge.getValue().impliesEqualityOnThatPosition(elem.getArguments())) {
					reportEquality(elem, c);
				}

			}
		}
	}


	@Override
	public WeqCongruenceClosure<ACTION, NODE, FUNCTION> join(final CongruenceClosure<NODE, FUNCTION> otherCC) {
		if (!(otherCC instanceof WeqCongruenceClosure)) {
			throw new IllegalArgumentException();
		}
		final WeqCongruenceClosure<ACTION, NODE, FUNCTION> other =
				(WeqCongruenceClosure<ACTION, NODE, FUNCTION>) otherCC;

		return new WeqCongruenceClosure<>(super.join(other), mWeakEquivalenceGraph.join(other.mWeakEquivalenceGraph));
	}

	@Override
	public WeqCongruenceClosure<ACTION, NODE, FUNCTION> meet(final CongruenceClosure<NODE, FUNCTION> otherCC) {
		if (!(otherCC instanceof WeqCongruenceClosure)) {
			throw new IllegalArgumentException();
		}
		final WeqCongruenceClosure<ACTION, NODE, FUNCTION> other =
				(WeqCongruenceClosure<ACTION, NODE, FUNCTION>) otherCC;

		final CongruenceClosure<NODE, FUNCTION> gPaMeet = super.meet(otherCC);
		if (gPaMeet.isInconsistent()) {
				return new WeqCongruenceClosure<>(true);
		}

		final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weqMeet =
				mWeakEquivalenceGraph.meet(other.mWeakEquivalenceGraph, gPaMeet);

		while (weqMeet.hasArrayEqualities()) {
			if (gPaMeet.isInconsistent()) {
				return new WeqCongruenceClosure<>(true);
			}
			final Entry<FUNCTION, FUNCTION> aeq = weqMeet.pollArrayEquality();
			gPaMeet.reportFunctionEquality(aeq.getKey(), aeq.getValue());
			weqMeet.reportChangeInGroundPartialArrangement((final CongruenceClosure<NODE, FUNCTION> cc)
						-> cc.reportFunctionEquality(aeq.getKey(), aeq.getValue()));
		}
		return new WeqCongruenceClosure<>(gPaMeet, weqMeet);
	}

	@Override
	public boolean sanityCheck() {
		boolean res = super.sanityCheck();
		if (mWeakEquivalenceGraph != null) {
			res &= mWeakEquivalenceGraph.sanityCheck();
		}
		return res;
	}

	@Override public String toString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(super.toString());
		sb.append("\n");
		sb.append("Weak equivalences:\n");
		sb.append(mWeakEquivalenceGraph.toString());
		return sb.toString();
	}

}