/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SMTTheoryState implements IAbstractState<SMTTheoryState>, IEqualityProvidingState {

	private final IPredicate mPredicate;

	private final SMTTheoryStateFactoryAndPredicateHelper mFactory;

	private final Set<IProgramVarOrConst> mPvocs;

	public SMTTheoryState(final IPredicate predicate, final Set<IProgramVarOrConst> variables,
			final SMTTheoryStateFactoryAndPredicateHelper factory) {
		mPredicate = predicate;
		mFactory = factory;
		mPvocs = variables;
	}

	@Override
	public SMTTheoryState addVariable(final IProgramVarOrConst variable) {
		final Set<IProgramVarOrConst> newPvocs = new HashSet<>(mPvocs);
		newPvocs.add(variable);
		return mFactory.getOrConstructState(mPredicate, newPvocs);
	}

	@Override
	public SMTTheoryState removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}

	@Override
	public SMTTheoryState addVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<IProgramVarOrConst> newPvocs = new HashSet<>(mPvocs);
		newPvocs.addAll(variables);
		return mFactory.getOrConstructState(mPredicate, newPvocs);
	}

	@Override
	public SMTTheoryState removeVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<TermVariable> termVariablesFromPvocs =
				variables.stream().map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());
		final IPredicate projectedPredicate = mFactory.projectExistentially(termVariablesFromPvocs, mPredicate);

		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mPvocs);
		newVariables.removeAll(variables);

		return mFactory.getOrConstructState(projectedPredicate, newVariables);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mPvocs.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mPvocs;
	}

	@Override
	public SMTTheoryState patch(final SMTTheoryState dominator) {
		final SMTTheoryState newState = removeVariables(dominator.getVariables());
		return newState.intersect(dominator);
	}

	@Override
	public SMTTheoryState intersect(final SMTTheoryState other) {
		return mFactory.conjoin(this, other);
	}

	@Override
	public SMTTheoryState union(final SMTTheoryState other) {
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
	public boolean isEqualTo(final SMTTheoryState other) {
		return (isSubsetOf(other) == SubsetResult.NON_STRICT && other.isSubsetOf(this) == SubsetResult.NON_STRICT)
				|| isSubsetOf(other) == SubsetResult.EQUAL;
	}

	@Override
	public de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult
			isSubsetOf(final SMTTheoryState other) {
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
		final Set<IProgramVarOrConst> newPvocs =
				mPvocs.stream().filter(pvoc -> (!(pvoc instanceof IProgramVar)) || freeVars.contains(pvoc.getTerm()))
						.collect(Collectors.toSet());
		return mFactory.getOrConstructState(mPredicate, newPvocs);
	}

	@Override
	public Term getTerm(final Script script) {
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
	public boolean impliesLiteral(final Term literalTerm) {
		return mFactory.impliesLiteral(this, literalTerm);
	}

	@Override
	public String toString() {
		return mPredicate.toString();
	}

	@Override
	public boolean areEqual(final Term t1, final Term t2) {
		final ManagedScript mgdScript = mFactory.getManagedScript();
		mgdScript.lock(this);
		final Term equalsTerm = mgdScript.term(this, "=", t1, t2);
		mgdScript.unlock(this);
		return impliesLiteral(equalsTerm);
	}

	@Override
	public boolean areUnequal(final Term t1, final Term t2) {
		final ManagedScript mgdScript = mFactory.getManagedScript();
		mgdScript.lock(this);
		final Term unequalsTerm = mgdScript.term(this, "distinct", t1, t2);
		mgdScript.unlock(this);
		return impliesLiteral(unequalsTerm);
	}

	@Override
	public IEqualityProvidingState join(final IEqualityProvidingState other) {
		return union((SMTTheoryState) other);
	}

	@Override
	public SMTTheoryState renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		throw new UnsupportedOperationException("not yet implemented");
	}
}
