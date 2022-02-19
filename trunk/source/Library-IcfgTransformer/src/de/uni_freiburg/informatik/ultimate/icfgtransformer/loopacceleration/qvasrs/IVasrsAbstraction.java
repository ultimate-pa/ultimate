package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.IVasrAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public interface IVasrsAbstraction<S> {

	/**
	 * Add a new transition between two states. This transition is modeled as a reset and addition vector pair.
	 * Representing changes to program variables and relations between program variables.
	 *
	 * @param transition
	 *            A new transition (p, [r, a], q). p, q being predicates and [r, a] is a pair of rational reset and
	 *            addition vectors.
	 */
	void addTransition(final Triple<Term, Pair<S[], S[]>, Term> transition);

	Set<Term> getStates();

	Set<Triple<Term, Pair<S[], S[]>, Term>> getTransitions();

	S[][] getSimulationMatrix();

	Term getPreState();

	Term getPostState();

	Map<IProgramVar, TermVariable> getInVars();

	Map<IProgramVar, TermVariable> getOutVars();

	IVasrAbstraction<S> getAbstraction();

	void setPrePostStates();

	void setPostState(Term post);

	void setPreState(Term pre);

}
