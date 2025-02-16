package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class RelationalInterferenceState {
	private final HashRelation<String, Term> mInterferenceMapHashRelation;
	private final ManagedScript mManagedScript;

	public RelationalInterferenceState(final ManagedScript script) {
		mInterferenceMapHashRelation = new HashRelation<>();
		mManagedScript = script;
	}

	public RelationalInterferenceState(final HashRelation<String, Term> interferenceRelation,
			final ManagedScript script) {
		mInterferenceMapHashRelation = new HashRelation<>(interferenceRelation);
		mManagedScript = script;
	}

	public Set<Term> getInterferencesForThread(final String threadName) {
		return mInterferenceMapHashRelation.getImage(threadName);
	}

	public void addInterference(final String threadName, final Term interference) {
		mInterferenceMapHashRelation.addPair(threadName, interference);
	}

	public boolean implies(final RelationalInterferenceState other) {
		for (final String thread : getInterferenceMapHashRelation().getDomain()) {
			if (!termsImply(getInterferencesForThread(thread), other.getInterferencesForThread(thread))) {
				return false;
			}
		}
		return true;
	}

	private boolean termsImply(final Set<Term> one, final Set<Term> two) {
		getManagedScript().lock(this);
		Term conjunctiveOneTerm = getManagedScript().term(this, "false");
		for (final Term oneTerm : one) {
			conjunctiveOneTerm = SmtUtils.or(getManagedScript().getScript(), conjunctiveOneTerm, oneTerm);

		}
		Term conjunctiveTwoTerm = getManagedScript().term(this, "false");
		for (final Term twoTerm : two) {
			conjunctiveTwoTerm = SmtUtils.or(getManagedScript().getScript(), conjunctiveTwoTerm, twoTerm);

		}
		getManagedScript().unlock(this);
		// TODO: check this locking (fails), unknown vars. related to my var creation in postoperator
		// mManagedScript.lock(this);
		// mManagedScript.push(this, 1);
		// mManagedScript.assertTerm(this, conjunctiveOneTerm);
		// mManagedScript.assertTerm(this, SmtUtils.not(mManagedScript.getScript(), conjunctiveTwoTerm));
		// final LBool checkSatResult = mManagedScript.checkSat(this);
		// mManagedScript.pop(this, 1);
		// mManagedScript.unlock(this);
		//
		// assert checkSatResult != LBool.UNKNOWN;
		//
		// return checkSatResult == LBool.UNSAT;
		return one.size() == two.size();
	}

	public HashRelation<String, Term> getInterferenceMapHashRelation() {
		return mInterferenceMapHashRelation;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public Set<String> termStrings() {
		final Set<String> termStrings = new HashSet<>();
		for (final String thread : mInterferenceMapHashRelation.getDomain()) {
			for (final Term threadTerm : getInterferencesForThread(thread)) {
				termStrings.add("Thread " + thread + ": " + threadTerm.toString());
			}
		}
		return termStrings;
	}
}
