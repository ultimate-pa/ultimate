package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

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

	public EqDisjunctiveConstraint(Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		mConstraints = new HashSet<>(constraintList);
	}

	public boolean isBottom() {
		// TODO Auto-generated method stub
		return false;
	}

	public void renameVariables(Map<Term, Term> substitutionMapping) {
		for (EqConstraint<ACTION, NODE, FUNCTION> constraint : mConstraints) {
			constraint.renameVariables(substitutionMapping);
		}
	}

	public void freeze() {
		// TODO Auto-generated method stub
		
	}

	public void projectExistentially(Set<TermVariable> varsToProjectAway) {
		// TODO Auto-generated method stub
		
	}

	public Set<EqConstraint<ACTION, NODE, FUNCTION>> getConstraints() {
		return mConstraints;
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
