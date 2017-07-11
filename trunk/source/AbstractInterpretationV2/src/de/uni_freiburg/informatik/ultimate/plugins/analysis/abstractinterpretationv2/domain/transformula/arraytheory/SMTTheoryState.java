package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class SMTTheoryState implements IAbstractState<SMTTheoryState, IProgramVarOrConst> {
	
	private final IPredicate mPredicate;
	
	private final SMTTheoryStateFactoryAndPredicateHelper mFactory;

	private final Set<IProgramVarOrConst> mPvocs;
	
	public SMTTheoryState(IPredicate predicate, Set<IProgramVarOrConst> variables, SMTTheoryStateFactoryAndPredicateHelper factory) {
		mPredicate = predicate;
		mFactory = factory;
		mPvocs = variables;
	}

	@Override
	public SMTTheoryState addVariable(final IProgramVarOrConst variable) {
		Set<IProgramVarOrConst> newPvocs = new HashSet<>(mPvocs);
		newPvocs.add(variable);
		return mFactory.getOrConstructState(mPredicate, newPvocs);
	}

	@Override
	public SMTTheoryState removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}

	@Override
	public SMTTheoryState addVariables(final Collection<IProgramVarOrConst> variables) {
		Set<IProgramVarOrConst> newPvocs = new HashSet<>(mPvocs);
		newPvocs.addAll(variables);
		return mFactory.getOrConstructState(mPredicate, newPvocs);
	}

	@Override
	public SMTTheoryState removeVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<TermVariable> termVariablesFromPvocs =
				variables.stream().map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());
		final IPredicate projectedPredicate =
				mFactory.projectExistentially(termVariablesFromPvocs, mPredicate);

		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mPvocs);
		newVariables.removeAll(variables);

		return mFactory.getOrConstructState(projectedPredicate, newVariables);
	}	

	@Override
	public boolean containsVariable(IProgramVarOrConst var) {
		return mPvocs.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mPvocs;
	}

	@Override
	public SMTTheoryState patch(SMTTheoryState dominator) {
		final SMTTheoryState newState = this.removeVariables(dominator.getVariables());
		return newState.intersect(dominator);
	}

	@Override
	public SMTTheoryState intersect(SMTTheoryState other) {
		return mFactory.conjoin(this, other);
	}

	@Override
	public SMTTheoryState union(SMTTheoryState other) {
		return mFactory.disjoinFlat(this, other);
	}

	@Override
	public boolean isEmpty() {
		return mPvocs.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return this == mFactory.getBottomState();
	}

	@Override
	public boolean isEqualTo(SMTTheoryState other) {
		return (this.isSubsetOf(other) == SubsetResult.NON_STRICT && other.isSubsetOf(this) == SubsetResult.NON_STRICT)
				|| this.isSubsetOf(other) == SubsetResult.EQUAL;
	}

	@Override
	public de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult isSubsetOf(
			SMTTheoryState other) {
		final boolean thisImpliesOther = mFactory.implies(this, other);
		final boolean otherImpliesThis = mFactory.implies(other, this);

		if (thisImpliesOther && otherImpliesThis) {
			return SubsetResult.EQUAL;
		}

		if (thisImpliesOther) {
			return SubsetResult.NON_STRICT;
		}
		
		return SubsetResult.NONE;
	}

	@Override
	public SMTTheoryState compact() {
		final List<TermVariable> freeVars = Arrays.asList(mPredicate.getFormula().getFreeVars());
		final Set<IProgramVarOrConst> newPvocs = mPvocs.stream()
				.filter(pvoc -> (!(pvoc instanceof IProgramVar)) || freeVars.contains(pvoc.getTerm()))
				.collect(Collectors.toSet());
		return mFactory.getOrConstructState(mPredicate, newPvocs);
	}

	@Override
	public Term getTerm(Script script) {
		return mPredicate.getFormula();
	}

	@Override
	public String toLogString() {
		return mPredicate.toString();
	}

	public IPredicate getPredicate() {
		return mPredicate;
	}

	/**
	 * Checks if the given term is implied by this state.
	 * 
	 * @param literalTerm
	 * @return
	 */
	public boolean impliesLiteral(Term literalTerm) {
		return mFactory.impliesLiteral(this, literalTerm);
	}

	@Override
	public String toString() {
		return mPredicate.toString();
	}
}
