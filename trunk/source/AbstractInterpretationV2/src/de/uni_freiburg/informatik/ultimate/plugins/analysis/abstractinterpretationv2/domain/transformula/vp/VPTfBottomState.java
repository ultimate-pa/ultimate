package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPTfBottomState extends VPTfState {

	public VPTfBottomState(Set<IProgramVar> vars) {
		super(null, Collections.emptyMap(), new HashRelation<VPArrayIdentifier, VPNodeIdentifier>(), 
				Collections.emptySet(),false, vars);
	}

	@Override
	public boolean tracksTerm(Term term) {
		assert false : "check for bottom before calling this! (right?)";
		return super.tracksTerm(term);
	}

	@Override
	public boolean isBottom() {
		return true;
	}

	@Override
	public boolean isTop() {
		return false;
	}

	@Override
	public TransFormula getTransFormula() {
		assert false : "check for bottom before asking for a Transformula";
		return null;
	}
}
