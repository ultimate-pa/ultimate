package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
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

	@Override
	public EqState<ACTION> addVariable(IProgramVarOrConst variable) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqState<ACTION> removeVariable(IProgramVarOrConst variable) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqState<ACTION> addVariables(Collection<IProgramVarOrConst> variables) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqState<ACTION> removeVariables(Collection<IProgramVarOrConst> variables) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean containsVariable(IProgramVarOrConst var) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		// TODO Auto-generated method stub
		return null;
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
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isBottom() {
		// TODO Auto-generated method stub
		return false;
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

}
