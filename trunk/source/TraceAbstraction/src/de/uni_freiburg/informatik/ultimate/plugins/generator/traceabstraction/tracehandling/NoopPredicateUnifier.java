package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A PredicateUnifier that does not unify any predicates, but just creates temporary predicates to be unified by another
 * PredicateUnifier later on.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class NoopPredicateUnifier implements IPredicateUnifier {

	private final PredicateFactory mPredicateFactory;
	private final Script mScript;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;

	public NoopPredicateUnifier(final PredicateFactory predicateFactory, final Script script) {
		mPredicateFactory = predicateFactory;
		mScript = script;
		mTruePredicate = getOrConstructPredicate(script.term("true"));
		mFalsePredicate = getOrConstructPredicate(script.term("false"));
	}

	@Override
	public IPredicate getTruePredicate() {
		return mTruePredicate;
	}

	@Override
	public IPredicate getFalsePredicate() {
		return mFalsePredicate;
	}

	@Override
	public IPredicate getOrConstructPredicateForConjunction(final Collection<IPredicate> conjunction) {
		return getOrConstructPredicate(
				SmtUtils.and(mScript, conjunction.stream().map(IPredicate::getFormula).collect(Collectors.toList())));
	}

	@Override
	public IPredicate getOrConstructPredicateForDisjunction(final Collection<IPredicate> disjunction) {
		return getOrConstructPredicate(
				SmtUtils.or(mScript, disjunction.stream().map(IPredicate::getFormula).collect(Collectors.toList())));
	}

	@Override
	public IPredicate getOrConstructPredicate(final Term term) {
		return mPredicateFactory.newSPredicate(null, term);
	}

	@Override
	public IPredicate getOrConstructPredicate(final IPredicate predicate) {
		return predicate;
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isIntricatePredicate(final IPredicate pred) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<IPredicate> cannibalize(final boolean splitNumericEqualities, final Term term) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<IPredicate> cannibalizeAll(final boolean splitNumericEqualities,
			final Collection<IPredicate> predicates) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IPredicateCoverageChecker getCoverageRelation() {
		return new IPredicateCoverageChecker() {
			@Override
			public Validity isCovered(final IPredicate lhs, final IPredicate rhs) {
				if (lhs.equals(mFalsePredicate) || rhs.equals(mTruePredicate)) {
					return Validity.VALID;
				}
				if (lhs.equals(mTruePredicate) && rhs.equals(mFalsePredicate)) {
					return Validity.INVALID;
				}
				return Validity.NOT_CHECKED;
			}

			@Override
			public Set<IPredicate> getCoveredPredicates(final IPredicate pred) {
				return new HashSet<>(Arrays.asList(pred, mFalsePredicate));
			}

			@Override
			public Set<IPredicate> getCoveringPredicates(final IPredicate pred) {
				return new HashSet<>(Arrays.asList(pred, mTruePredicate));
			}

			@Override
			public IPartialComparator<IPredicate> getPartialComperator() {
				throw new UnsupportedOperationException();
			}

			@Override
			public HashRelation<IPredicate, IPredicate> getCopyOfImplicationRelation() {
				return new HashRelation<>();
			}
		};
	}

	@Override
	public IStatisticsDataProvider getPredicateUnifierBenchmark() {
		throw new UnsupportedOperationException();
	}

	@Override
	public BasicPredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	@Override
	public boolean isRepresentative(final IPredicate pred) {
		return true;
	}

	@Override
	public IPredicate constructNewPredicate(final Term term, final Map<IPredicate, Validity> impliedPredicates,
			final Map<IPredicate, Validity> expliedPredicates) {
		return getOrConstructPredicate(term);
	}
}
