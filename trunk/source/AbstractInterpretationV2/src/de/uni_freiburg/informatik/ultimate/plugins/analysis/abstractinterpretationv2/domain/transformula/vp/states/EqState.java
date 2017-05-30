package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
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
	
	Set<IProgramVarOrConst> mVariables = new HashSet<>();

//	private final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> mConstraint;
	private final EqConstraint<ACTION, EqNode, EqFunction> mConstraint;

	private final EqStateFactory<ACTION> mFactory;
	
	
	public EqState(EqConstraint<ACTION, EqNode, EqFunction> constraint, 
			EqNodeAndFunctionFactory eqNodeAndFunctionFactory, EqStateFactory<ACTION> eqStateFactory) {
		mConstraint = constraint;
		mFactory = eqStateFactory;
	}

	@Override
	public EqState<ACTION> addVariable(IProgramVarOrConst variable) {
		mVariables.add(variable);
		return this;
	}

	@Override
	public EqState<ACTION> removeVariable(IProgramVarOrConst variable) {
		mVariables.remove(variable);
		return this;
	}

	@Override
	public EqState<ACTION> addVariables(Collection<IProgramVarOrConst> variables) {
		mVariables.addAll(variables);
		return this;
	}

	@Override
	public EqState<ACTION> removeVariables(Collection<IProgramVarOrConst> variables) {
		final Set<TermVariable> termVariablesFromPvocs = variables.stream()
				.map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());
		final EqConstraint<ACTION, EqNode, EqFunction> projectedConstraint = 
				mConstraint.projectExistentially(termVariablesFromPvocs);
		
		
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mVariables);
		newVariables.removeAll(variables);
		
		return mFactory.getEqState(projectedConstraint, newVariables);
	}

	@Override
	public boolean containsVariable(IProgramVarOrConst var) {
		return mVariables.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mVariables);
	}

	@Override
	public EqState<ACTION> patch(EqState<ACTION> dominator) {
		EqState<ACTION> newState = removeVariables(dominator.getVariables());
		return newState.intersect(dominator);
	}

	@Override
	public EqState<ACTION> intersect(EqState<ACTION> other) {
		final EqConstraint<ACTION, EqNode, EqFunction> newConstraint = 
				mFactory.getEqConstraintFactory().conjoinFlat(this.getConstraint(), other.getConstraint());
		
		return mFactory.getEqState(newConstraint, newConstraint.getPvocs());
	}

	@Override
	public EqState<ACTION> union(EqState<ACTION> other) {
		final EqConstraint<ACTION, EqNode, EqFunction> newConstraint = 
				mFactory.getEqConstraintFactory().disjoinFlat(this.getConstraint(), other.getConstraint());
		
		return mFactory.getEqState(newConstraint, newConstraint.getPvocs());

	}
	
	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mConstraint.isBottom();
	}

	@Override
	public boolean isEqualTo(EqState<ACTION> other) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult isSubsetOf(
			EqState<ACTION> other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqState<ACTION> compact() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term getTerm(Script script) {
		return mConstraint.getTerm(script);
	}

	@Override
	public String toLogString() {
		return mConstraint.toString();
	}

	public EqConstraint<ACTION, EqNode, EqFunction> getConstraint() {
		return mConstraint;
	}

	public EqPredicate<ACTION> toEqPredicate() {
		return new EqPredicate<>(
				mFactory.getEqConstraintFactory().getDisjunctiveConstraint(Collections.singleton(mConstraint)),
				mConstraint.getVariables(),
//				mVariables.stream() // TODO: maybe ask the constraint for its variables?
//					.filter(pvoc -> (pvoc instanceof IProgramVar))
//					.map(pvoc -> ((IProgramVar) pvoc))
//					.collect(Collectors.toSet()),
				null); // TODO: what procedures does the predicate need?
	}

	public boolean areUnequal(EqNode node1, EqNode node2) {
		return mConstraint.areUnequal(node1, node2);
	}

	public boolean areEqual(Term term1, Term term2) {
		if (term1.getSort().isArraySort()) {
			assert term2.getSort().isArraySort();
			final EqFunction node1 = mFactory.getEqNodeAndFunctionFactory().getEqFunction(term1);
			final EqFunction node2 = mFactory.getEqNodeAndFunctionFactory().getEqFunction(term2);
			return mConstraint.areEqual(node1, node2);
		} else {
			final EqNode node1 = mFactory.getEqNodeAndFunctionFactory().getEqNode(term1);
			final EqNode node2 = mFactory.getEqNodeAndFunctionFactory().getEqNode(term2);
			return mConstraint.areEqual(node1, node2);
		}
	}

	public boolean areUnequal(Term term1, Term term2) {
		if (term1.getSort().isArraySort()) {
			assert term2.getSort().isArraySort();
			final EqFunction node1 = mFactory.getEqNodeAndFunctionFactory().getEqFunction(term1);
			final EqFunction node2 = mFactory.getEqNodeAndFunctionFactory().getEqFunction(term2);
			return mConstraint.areUnequal(node1, node2);
		} else {
			final EqNode node1 = mFactory.getEqNodeAndFunctionFactory().getEqNode(term1);
			final EqNode node2 = mFactory.getEqNodeAndFunctionFactory().getEqNode(term2);
			return mConstraint.areUnequal(node1, node2);
		}
	}

}
