package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class EqDisjunctiveConstraint<
				ACTION extends IIcfgTransition<IcfgLocation>, 
				NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
				FUNCTION extends IEqFunctionIdentifier<FUNCTION>> 
     			 	extends AbstractMultiState<EqConstraint<ACTION, NODE, FUNCTION>, IProgramVarOrConst>{

	Set<EqConstraint<ACTION, NODE, FUNCTION>> mConstraints;

	private EqConstraintFactory<ACTION, NODE, FUNCTION> mEqConstraintFactory;

	public EqDisjunctiveConstraint(Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		mConstraints = new HashSet<>(constraintList);
	}

	public boolean isBottom() {
		return mConstraints.stream().map(conjConstraint -> conjConstraint.isBottom()).reduce((a, b) -> a && b).get();
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> renameVariables(Map<Term, Term> substitutionMapping) {
		for (EqConstraint<ACTION, NODE, FUNCTION> constraint : mConstraints) {
			constraint.renameVariables(substitutionMapping);
		}
		return this;
	}


	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> projectExistentially(Set<TermVariable> varsToProjectAway) {
		return mEqConstraintFactory.getDisjunctiveConstraint(
				mConstraints.stream()
					.map(conjConstraint -> conjConstraint.projectExistentially(varsToProjectAway))
					.collect(Collectors.toSet()));
	}

	public Set<EqConstraint<ACTION, NODE, FUNCTION>> getConstraints() {
		return mConstraints;
	}

	/**
	 * Return the strongest conjunctive EqConstraint that is implied by all elements of mConstraints.
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> flatten() {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Only does the cast, other than that just calls @see AbstractMultistate.union
	 * 
	 */
	@Override
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> union(
			AbstractMultiState<EqConstraint<ACTION, NODE, FUNCTION>, IProgramVarOrConst> other) {
		assert other instanceof EqDisjunctiveConstraint;
		return (EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>) super.union(other);
	}
	
	
	
//	/**
//	 * Create a new {@link AbstractMultiState} by applying some function to each pair of states from this
//	 * {@link AbstractMultiState} and some other {@link AbstractMultiState} (i.e., the first argument is a state from
//	 * this instance). If the resulting set of states does not differ from this state, return this state. If it differs,
//	 * create a new {@link AbstractMultiState} that retains as many as <code>maxSize</code> disjunctive states.
//	 */
//	private AbstractMultiState<STATE, VARDECL> crossProduct(final BiFunction<STATE, STATE, STATE> funCreateState,
//			final AbstractMultiState<STATE, VARDECL> otherMultiState, final int maxSize) {
//		final Set<STATE> newSet = newSet(mStates.size() * otherMultiState.mStates.size());
//		for (final STATE localState : mStates) {
//			for (final STATE otherState : otherMultiState.mStates) {
//				newSet.add(funCreateState.apply(localState, otherState));
//			}
//		}
//		if (newSet.equals(mStates)) {
//			return this;
//		}
//		return new AbstractMultiState<>(maxSize, getMaximalElements(newSet));
//	}
	
	
}
