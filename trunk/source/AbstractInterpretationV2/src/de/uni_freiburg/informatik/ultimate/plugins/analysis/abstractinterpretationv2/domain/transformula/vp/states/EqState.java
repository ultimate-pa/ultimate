package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqState<ACTION extends IIcfgTransition<IcfgLocation>> 
		implements IAbstractState<EqState<ACTION>, IProgramVarOrConst> {
	
	Set<IProgramVarOrConst> mVariables = new HashSet<>();

	private final EqConstraint<ACTION, EqNode, EqFunction> mConstraint;
	
	
	public EqState(EqConstraint<ACTION, EqNode, EqFunction> constraint) {
		mConstraint = constraint;
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
		mVariables.removeAll(variables);
		return this;
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqState<ACTION> intersect(EqState<ACTION> other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqState<ACTION> union(EqState<ACTION> other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mConstraint instanceof EqBottomConstraint;
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toLogString() {
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getConstraint() {
		// TODO Auto-generated method stub
		return null;
	}

	public EqPredicate<ACTION> toEqPredicate() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean areUnequal(EqNode accessingNode1, EqNode accessingNode2) {
		// TODO Auto-generated method stub
		assert false;
		return false;
	}

	public boolean areEqual(Term oneElement, Term otherElement) {
		// TODO Auto-generated method stub
		assert false;
		return false;
	}

	public boolean areUnequal(Term oneElement, Term otherElement) {
		// TODO Auto-generated method stub
		assert false;
		return false;
	}

}
