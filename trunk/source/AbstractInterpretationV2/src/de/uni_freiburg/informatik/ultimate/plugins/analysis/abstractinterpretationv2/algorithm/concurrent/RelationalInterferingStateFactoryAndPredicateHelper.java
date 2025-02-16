package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RelationalInterferingStateFactoryAndPredicateHelper {

	private final BasicPredicateFactory mBasicPredicateFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mMgdScript;
	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_QUICK;
	private final IUltimateServiceProvider mServices;

	private final Map<Term, IPredicate> mTermToPredicate;
	private final IDomain mSifaDomain;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;
	private final RelationalInterferingDomain mRelInterferingDomain;

	private final RelationalInterferenceState mInterferences;

	public RelationalInterferingStateFactoryAndPredicateHelper(final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final IDomain sifaDomain, final RelationalInterferingDomain relInterferingDomain,
			final BasicPredicateFactory predicateFactory, final RelationalInterferenceState interferences,
			final ThreadInstanceCounterFactory threadInstanceCounterFactory) {
		mCsToolkit = csToolkit;
		mMgdScript = csToolkit.getManagedScript();
		mServices = services;
		mTermToPredicate = new HashMap<>();
		mBasicPredicateFactory = predicateFactory;
		mThreadInstanceCounterFactory = threadInstanceCounterFactory;
		mSifaDomain = sifaDomain;
		mRelInterferingDomain = relInterferingDomain;
		mInterferences = interferences;
	}

	public Term getFalseTerm() {
		mCsToolkit.getManagedScript().lock(this);
		final var falseTerm = mCsToolkit.getManagedScript().term(this, "false");
		mCsToolkit.getManagedScript().unlock(this);
		return falseTerm;
	}

	public RelationalInterferingState getOrConstructState(final Term resTerm,
			final ImmutableSet<IProgramVarOrConst> variables, final ThreadInstanceCounter threadCounter) {

		final IPredicate pred = getOrConstructPredicate(resTerm);
		return getOrConstructState(pred, variables, threadCounter);
	}

	private IPredicate getOrConstructPredicate(final Term resTerm) {

		IPredicate pred = mTermToPredicate.get(resTerm);
		if (pred == null) {
			pred = mBasicPredicateFactory.newPredicate(resTerm);
		}
		return pred;
	}

	public RelationalInterferingState getOrConstructState(final IPredicate predicate,
			final ImmutableSet<IProgramVarOrConst> newPvocs, final ThreadInstanceCounter threadCounter) {
		return new RelationalInterferingState(predicate, newPvocs,
				new ThreadInstanceCounter(threadCounter.getThreadInstances()), this, mSifaDomain, mInterferences);
	}

	public RelationalInterferingState getTopState() {
		final Set<IProgramVarOrConst> variables = new HashSet<>(mCsToolkit.getSymbolTable().getGlobals());
		mCsToolkit.getManagedScript().lock(this);
		final var newState = getOrConstructState(mCsToolkit.getManagedScript().term(this, "true"),
				ImmutableSet.of(variables), mThreadInstanceCounterFactory.createTopState());
		mCsToolkit.getManagedScript().unlock(this);
		return newState;
	}

	public RelationalInterferingState getBottomState() {
		final Set<IProgramVarOrConst> variables = new HashSet<>(mCsToolkit.getSymbolTable().getGlobals());
		mCsToolkit.getManagedScript().lock(this);
		final var newState = getOrConstructState(mCsToolkit.getManagedScript().term(this, "false"),
				ImmutableSet.of(variables), mThreadInstanceCounterFactory.createBottomState());
		mCsToolkit.getManagedScript().unlock(this);
		return newState;
	}

	public RelationalInterferingState getBottomPreconditionState() {
		final Set<IProgramVarOrConst> variables = new HashSet<>(mCsToolkit.getSymbolTable().getGlobals());
		mCsToolkit.getManagedScript().lock(this);
		final var newState = getOrConstructState(mCsToolkit.getManagedScript().term(this, "true"),
				ImmutableSet.of(variables), mThreadInstanceCounterFactory.createBottomState());
		mCsToolkit.getManagedScript().unlock(this);
		return newState;
	}

	public RelationalInterferingState widen(final RelationalInterferingState first,
			final RelationalInterferingState second) {
		return mRelInterferingDomain.getWideningOperator().apply(first, second);
	}

	public IPredicate disjunctiveJoin(final IPredicate first, final IPredicate second) {
		return mBasicPredicateFactory.or(mSimplificationTechnique, first, second);
	}

	public IPredicate conjunctiveJoin(final RelationalInterferingState first, final RelationalInterferingState second) {
		if (first.isBottom()) {
			return first.getPredicate();
		}
		if (second.isBottom()) {
			return second.getPredicate();
		}

		return mBasicPredicateFactory.and(mSimplificationTechnique, first.getPredicate(), second.getPredicate());

	}

	public IPredicate projectExistentially(final Set<TermVariable> varsToProject, final IPredicate predicate) {
		final Term withQuant = SmtUtils.quantifier(mMgdScript.getScript(), QuantifiedFormula.EXISTS, varsToProject,
				predicate.getFormula());

		return mBasicPredicateFactory.newPredicate(PartialQuantifierElimination.eliminate(mServices, mMgdScript,
				withQuant, SimplificationTechnique.SIMPLIFY_DDA2));
	}

	public ManagedScript getManagedScript() {
		return mMgdScript;
	}

}
