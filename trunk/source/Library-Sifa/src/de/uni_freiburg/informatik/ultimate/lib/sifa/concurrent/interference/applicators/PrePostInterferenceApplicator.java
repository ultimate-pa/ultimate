package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.applicators;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PrePostInterferenceApplicator implements IInterferenceApplicator {

	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public PrePostInterferenceApplicator(final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IPredicate apply(final IPredicate state, final Collection<GuardedPredicate> predicates, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		return InterferenceUtils.applyUntilFixpoint(state, predicates, domain, wideningThreshold, stats,
				this::applyPrePost);
	}

	private IPredicate applyPrePost(final IPredicate frontier, final GuardedPredicate predicate) {
		final Script script = mManagedScript.getScript();
		if (SmtUtils.isFalseLiteral(predicate.effect().getFormula())) {
			return mPredicateFactory.newPredicate(script.term("false"));
		}
		if (!predicate.hasGuard()) {
			return predicate.effect();
		}
		for (final Term frontierDisjunct : SmtUtils.getDisjuncts(frontier.getFormula())) {
			final Term guardedState =
					SmtUtils.andWithExtendedLocalSimplification(script, frontierDisjunct, predicate.guard().getFormula());
			if (!SmtUtils.isFalseLiteral(guardedState) && SmtUtils.checkSatTerm(script, guardedState) != Script.LBool.UNSAT) {
				return predicate.effect();
			}
		}
		return mPredicateFactory.newPredicate(script.term("false"));
	}
}
