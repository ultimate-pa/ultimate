package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

class WeqCongruenceClosure<ACTION extends IIcfgTransition<IcfgLocation>,
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>>
		extends CongruenceClosure<NODE, FUNCTION> {

	private final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> mWeakEquivalenceGraph;

	public WeqCongruenceClosure(final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		super();
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(factory);
	}


	public Term getTerm(final Script script) {
		final List<Term> allConjuncts =  new ArrayList<>();
		allConjuncts.addAll(EqConstraint.partialArrangementToCube(script, this));

		final List<Term> weakEqConstraints = mWeakEquivalenceGraph.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result= Util.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
			return result;
	}


	public void renameVariables(final Map<Term, Term> substitutionMapping) {
		transformElementsAndFunctions(
				node -> node.renameVariables(substitutionMapping),
				function -> function.renameVariables(substitutionMapping));
		mWeakEquivalenceGraph.renameVariables(substitutionMapping);
	}


	public void havocFunction(final FUNCTION functionToHavoc) {
	}


	public void reportWeakEquivalence(final FUNCTION array1, final FUNCTION array2, final List<NODE> storeIndex) {
		for (final NODE storeIndexNode : storeIndex) {
			getRepresentativeAndAddElementIfNeeded(storeIndexNode);
		}
		getRepresentativeAndAddFunctionIfNeeded(array1);
		getRepresentativeAndAddFunctionIfNeeded(array2);
		mWeakEquivalenceGraph.reportWeakEquivalence(array1, array2, storeIndex);
	}


	/**
	 *
	 *
	 * @param original
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE, FUNCTION> original,
			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weqGraph) {
		super(original);
		mWeakEquivalenceGraph = weqGraph;
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
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(original.mWeakEquivalenceGraph);
	}

	@Override
	protected boolean reportEqualityRec(final NODE node1, final NODE node2) {
		boolean madeChanges = false;
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

		madeChanges |= super.reportEqualityRec(node1, node2);
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
		// making a copy of the ground partial arrangement here, just to be safe..
		mWeakEquivalenceGraph.projectFunction(func, new WeqCongruenceClosure<>(this));

		return super.removeFunction(func);
	}


	@Override
	public boolean removeElement(final NODE elem) {
		// making a copy of the ground partial arrangement here, just to be safe..
		mWeakEquivalenceGraph.projectElement(elem, new WeqCongruenceClosure<>(this));

		return super.removeElement(elem);

	}


	@Override
	protected void registerNewElement(NODE elem) {
		// TODO Auto-generated method stub
		super.registerNewElement(elem);
	}


	@Override
	public WeqCongruenceClosure<ACTION, NODE, FUNCTION> join(final CongruenceClosure<NODE, FUNCTION> other) {
		return new WeqCongruenceClosure<>(super.join(other), mWeakEquivalenceGraph);
	}

	@Override
	public WeqCongruenceClosure<ACTION, NODE, FUNCTION> meet(final CongruenceClosure<NODE, FUNCTION> other) {
		return new WeqCongruenceClosure<>(super.meet(other), mWeakEquivalenceGraph);
	}

	@Override public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(super.toString());
		sb.append("\n");
		sb.append("Weak equivalences:\n");
		sb.append(mWeakEquivalenceGraph.toString());
		return sb.toString();
	}

}