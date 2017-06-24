package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;

public class EqState<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractState<EqState<ACTION>, IProgramVarOrConst> {

	/**
	 * The variables and constants that this state has "for the abstract interpretation"/"as an IAbstractState".
	 * Note that these should be related but need not be identical to mConstraint.getPvocs(..).
	 */
	private final Set<IProgramVarOrConst> mPvocs;

	// private final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> mConstraint;
	private final EqConstraint<ACTION, EqNode, EqFunction> mConstraint;

	private final EqStateFactory<ACTION> mFactory;

	public EqState(final EqConstraint<ACTION, EqNode, EqFunction> constraint,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, 
			final EqStateFactory<ACTION> eqStateFactory,
			final Set<IProgramVarOrConst> variables) {
		mConstraint = constraint;
		mFactory = eqStateFactory;
		mPvocs = new HashSet<>(variables);
	}

	@Override
	public EqState<ACTION> addVariable(final IProgramVarOrConst variable) {
		mPvocs.add(variable);
		return this;
	}

	@Override
	public EqState<ACTION> removeVariable(final IProgramVarOrConst variable) {
		mPvocs.remove(variable);
		return this;
	}

	@Override
	public EqState<ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		mPvocs.addAll(variables);
		return this;
	}

	@Override
	public EqState<ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<TermVariable> termVariablesFromPvocs =
				variables.stream().map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());
		final EqConstraint<ACTION, EqNode, EqFunction> projectedConstraint =
				mConstraint.projectExistentially(termVariablesFromPvocs);

		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mPvocs);
		newVariables.removeAll(variables);

		return mFactory.getEqState(projectedConstraint, newVariables);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mPvocs.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mPvocs);
	}

	@Override
	public EqState<ACTION> patch(final EqState<ACTION> dominator) {
		final EqState<ACTION> newState = this.removeVariables(dominator.getVariables());
		return newState.intersect(dominator);
	}

	@Override
	public EqState<ACTION> intersect(final EqState<ACTION> other) {
		final EqConstraint<ACTION, EqNode, EqFunction> newConstraint =
				mFactory.getEqConstraintFactory().conjoinFlat(this.getConstraint(), other.getConstraint());

		return mFactory.getEqState(newConstraint, newConstraint.getPvocs(mFactory.getSymbolTable()));
	}

	@Override
	public EqState<ACTION> union(final EqState<ACTION> other) {
		final EqConstraint<ACTION, EqNode, EqFunction> newConstraint =
				mFactory.getEqConstraintFactory().disjoinFlat(this.getConstraint(), other.getConstraint());

		return mFactory.getEqState(newConstraint, newConstraint.getPvocs(mFactory.getSymbolTable()));

	}

	@Override
	public boolean isEmpty() {
		return mPvocs.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mConstraint.isBottom();
	}

	@Override
	public boolean isEqualTo(final EqState<ACTION> other) {
		return this.isSubsetOf(other) == SubsetResult.NON_STRICT && other.isSubsetOf(this) == SubsetResult.NON_STRICT;
	}

	@Override
	public SubsetResult
			isSubsetOf(final EqState<ACTION> other) {
		// TODO
//		final EqConstraintFactory<ACTION, EqNode, EqFunction> constraintFactory = mFactory.getEqConstraintFactory();
//		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> intersectionWithComplement = 
//				constraintFactory.conjoinDisjunctiveConstraints(
//						toList(constraintFactory.getDisjunctiveConstraint(toList(mConstraint)), 
//								constraintFactory.complement(other.getConstraint())));
//		if (intersectionWithComplement.isBottom()) {
//			return SubsetResult.
//			
//		}
//		return null;
		return SubsetResult.NONE;
	}
	
	@SafeVarargs
	private static <E> List<E> toList(final E... elems) {
		return Arrays.asList(elems);
	}

	@Override
	public EqState<ACTION> compact() {
		return this;
	}

	@Override
	public Term getTerm(final Script script) {
		return mConstraint.getTerm(script);
	}

	@Override
	public String toLogString() {
		return mConstraint.toString();
	}
	
	@Override 
	public String toString() {
		return toLogString();
	}

	public EqConstraint<ACTION, EqNode, EqFunction> getConstraint() {
		return mConstraint;
	}

	public EqPredicate<ACTION> toEqPredicate() {
		return new EqPredicate<>(
				mFactory.getEqConstraintFactory().getDisjunctiveConstraint(Collections.singleton(mConstraint)),
				mConstraint.getVariables(mFactory.getSymbolTable()),
				// mVariables.stream()
				// .filter(pvoc -> (pvoc instanceof IProgramVar))
				// .map(pvoc -> ((IProgramVar) pvoc))
				// .collect(Collectors.toSet()),
				null); // TODO: what procedures does the predicate need?
	}

	public boolean areUnequal(final EqNode node1, final EqNode node2) {
		return mConstraint.areUnequal(node1, node2);
	}

	public boolean areEqual(final Term term1, final Term term2) {
		if (term1.getSort().isArraySort()) {
			assert term2.getSort().isArraySort();
			final EqFunction node1 = mFactory.getEqNodeAndFunctionFactory().getExistingEqFunction(term1);
			final EqFunction node2 = mFactory.getEqNodeAndFunctionFactory().getExistingEqFunction(term2);
			return mConstraint.areEqual(node1, node2);
		}
		final EqNode node1 = mFactory.getEqNodeAndFunctionFactory().getExistingEqNode(term1);
		final EqNode node2 = mFactory.getEqNodeAndFunctionFactory().getExistingEqNode(term2);
		return mConstraint.areEqual(node1, node2);
	}

	public boolean areUnequal(final Term term1, final Term term2) {
		if (term1.getSort().isArraySort()) {
			assert term2.getSort().isArraySort();
			final EqFunction node1 = mFactory.getEqNodeAndFunctionFactory().getExistingEqFunction(term1);
			final EqFunction node2 = mFactory.getEqNodeAndFunctionFactory().getExistingEqFunction(term2);
			return mConstraint.areUnequal(node1, node2);
		}
		final EqNode node1 = mFactory.getEqNodeAndFunctionFactory().getExistingEqNode(term1);
		final EqNode node2 = mFactory.getEqNodeAndFunctionFactory().getExistingEqNode(term2);
		return mConstraint.areUnequal(node1, node2);
	}

}
