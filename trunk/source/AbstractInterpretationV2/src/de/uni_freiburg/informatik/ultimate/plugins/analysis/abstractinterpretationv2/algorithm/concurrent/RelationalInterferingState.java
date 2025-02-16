package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermEquivalence;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RelationalInterferingState implements IAbstractState<RelationalInterferingState> {

	private final IDomain mSifaDomain;
	private final IPredicate mPredicate;
	private final RelationalInterferingStateFactoryAndPredicateHelper mFactory;
	private final ImmutableSet<IProgramVarOrConst> mPvarsOrConsts;
	private final ThreadInstanceCounter mThreadInstanceCounter;

	private final RelationalInterferenceState mInterferences;

	public RelationalInterferingState(final IPredicate predicate, final ImmutableSet<IProgramVarOrConst> variables,
			final ThreadInstanceCounter threadcounter,
			final RelationalInterferingStateFactoryAndPredicateHelper factory, final IDomain sifaDomain,
			final RelationalInterferenceState interferences) {
		mSifaDomain = sifaDomain;
		mPredicate = predicate;
		mPvarsOrConsts = variables;
		mThreadInstanceCounter = threadcounter;
		mFactory = factory;
		mInterferences = interferences;
	}

	public Set<Term> getInterferencesForThread(final String threadName) {
		return mInterferences.getInterferencesForThread(threadName);
	}

	public void addInterference(final String threadName, final Term interference) {
		mInterferences.addInterference(threadName, interference);
	}

	public IPredicate getPredicate() {
		return mPredicate;
	}

	public ThreadInstanceCounter getThreadInstanceState() {
		return mThreadInstanceCounter;
	}

	@Override
	public RelationalInterferingState addVariable(final IProgramVarOrConst variable) {
		final Set<IProgramVarOrConst> newPvarsOrConsts = new HashSet<>(mPvarsOrConsts);
		newPvarsOrConsts.add(variable);
		return mFactory.getOrConstructState(mPredicate, ImmutableSet.of(newPvarsOrConsts), mThreadInstanceCounter);
	}

	@Override
	public RelationalInterferingState removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}

	@Override
	public RelationalInterferingState addVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<IProgramVarOrConst> newPvarsOrConsts = new HashSet<>(mPvarsOrConsts);
		newPvarsOrConsts.addAll(variables);
		return mFactory.getOrConstructState(mPredicate, ImmutableSet.of(newPvarsOrConsts), mThreadInstanceCounter);
	}

	@Override
	public RelationalInterferingState removeVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<TermVariable> termVariablesFromPvocs =
				variables.stream().map(pvoc -> (TermVariable) pvoc.getTerm()).collect(Collectors.toSet());

		final IPredicate projectedPredicate = mFactory.projectExistentially(termVariablesFromPvocs, mPredicate);

		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mPvarsOrConsts);
		newVariables.removeAll(variables);

		return mFactory.getOrConstructState(projectedPredicate, ImmutableSet.of(newVariables), mThreadInstanceCounter);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mPvarsOrConsts.contains(var);
	}

	@Override
	public ImmutableSet<IProgramVarOrConst> getVariables() {
		return mPvarsOrConsts;
	}

	@Override
	public RelationalInterferingState patch(final RelationalInterferingState dominator) {
		final RelationalInterferingState newState = removeVariables(dominator.getVariables());
		return newState.intersect(dominator);
	}

	@Override
	public RelationalInterferingState intersect(final RelationalInterferingState other) {
		final Set<IProgramVarOrConst> varUnion = new HashSet<>(mPvarsOrConsts);
		varUnion.addAll(other.getVariables());
		// TODO: union threads?
		return mFactory.getOrConstructState(mFactory.conjunctiveJoin(this, other), ImmutableSet.of(varUnion),
				getThreadInstanceState().union(other.getThreadInstanceState()));
	}

	@Override
	public RelationalInterferingState union(final RelationalInterferingState other) {
		final Set<IProgramVarOrConst> varUnion = new HashSet<>(mPvarsOrConsts);
		varUnion.addAll(other.getVariables());
		return mFactory.getOrConstructState(mFactory.disjunctiveJoin(getPredicate(), other.getPredicate()),
				ImmutableSet.of(varUnion), getThreadInstanceState().union(other.getThreadInstanceState()));
	}

	@Override
	public boolean isEmpty() {
		return mPvarsOrConsts.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return new TermEquivalence().equal(getPredicate().getFormula(), mFactory.getFalseTerm());
	}

	@Override
	public boolean isEqualTo(final RelationalInterferingState other) {
		return isSubsetOf(other) == SubsetResult.NON_STRICT && other.isSubsetOf(this) == SubsetResult.NON_STRICT;
	}

	@Override
	public SubsetResult isSubsetOf(final RelationalInterferingState other) {
		final var result = mSifaDomain.isSubsetEq(getPredicate(), other.getPredicate());
		if (result.isTrueForAbstraction()) {
			return SubsetResult.NON_STRICT;
		}
		return SubsetResult.NONE;
	}

	@Override
	public RelationalInterferingState compact() {
		final List<TermVariable> freeVars = Arrays.asList(mPredicate.getFormula().getFreeVars());
		final ImmutableSet<IProgramVarOrConst> newPvocs = mPvarsOrConsts.stream()
				.filter(pvoc -> !(pvoc instanceof IProgramVar) || freeVars.contains(pvoc.getTerm()))
				.collect(ImmutableSet.collector());
		return mFactory.getOrConstructState(mPredicate, newPvocs, mThreadInstanceCounter);
	}

	@Override
	public RelationalInterferingState renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public Term getTerm(final Script script) {
		return mPredicate.getFormula();
	}

	// TODO: add thread/loc information
	@Override
	public String toLogString() {
		return mPredicate.toString();
	}

	// TODO: add thread/loc information
	@Override
	public String toString() {
		return mPredicate.toString();
	}

}
