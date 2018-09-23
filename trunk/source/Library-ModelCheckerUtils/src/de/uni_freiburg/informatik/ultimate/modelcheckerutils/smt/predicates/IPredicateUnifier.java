/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Data structure that stores for each term an unique predicate. Initially an {@link IPredicateUnifier} constructs a
 * "true" predicate and a "false" predicate.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IPredicateUnifier {

	IPredicate getTruePredicate();

	IPredicate getFalsePredicate();

	/**
	 * GetOrConstruct a predicate that is a conjunction of IPredicates that were construction by (resp. declared in)
	 * this PredicateUnifier.
	 */
	IPredicate getOrConstructPredicateForConjunction(Collection<IPredicate> conjunction);

	/**
	 * GetOrConstruct a predicate that is a disjunction of IPredicates that were constructed by (resp. declared in) this
	 * PredicateUnifier.
	 */
	IPredicate getOrConstructPredicateForDisjunction(Collection<IPredicate> disjunction);

	/**
	 * Get the predicate for a term.
	 */
	IPredicate getOrConstructPredicate(Term term);

	/**
	 * Get a unified version of a predicate.
	 */
	IPredicate getOrConstructPredicate(IPredicate predicate);

	String collectPredicateUnifierStatistics();

	/**
	 * We call a predicate "intricate" if we were unable to find out if it is equivalent to "true" or if we were unable
	 * to find out it it is equivalent to "false".
	 */
	boolean isIntricatePredicate(IPredicate pred);

	/**
	 * Given a term "cut up" all its conjuncts. We bring the term in CNF and return an IPredicate for each conjunct.
	 */
	Set<IPredicate> cannibalize(boolean splitNumericEqualities, Term term);

	Set<IPredicate> cannibalizeAll(boolean splitNumericEqualities, Collection<IPredicate> predicates);

	IPredicateCoverageChecker getCoverageRelation();

	IStatisticsDataProvider getPredicateUnifierBenchmark();

	/**
	 * @return the predicateFactory
	 */
	BasicPredicateFactory getPredicateFactory();

	/**
	 * Return true iff pred is the representative IPredicate for the Term pred.getFormula().
	 */
	boolean isRepresentative(final IPredicate pred);

	/**
	 * Construct a new predicate for the given term. The term may not be unified by this {@link IPredicateUnifier}, but
	 * is assumed to be unknown.
	 *
	 * @param term
	 *            Term for which new predicate is constructed. This term has to be simplified (resp. will not be further
	 *            simplified) and has to be different (not semantically equivalent) from all predicates known by this
	 *            predicate unifier.
	 * @param impliedPredicates
	 *            Result of the implication (term ==> p) for each known predicate p.
	 * @param expliedPredicates
	 *            Result of the implication (p ==> term) for each known predicate p.
	 * @return The predicate that was constructed for the term p.
	 */
	IPredicate constructNewPredicate(final Term term, final Map<IPredicate, Validity> impliedPredicates,
			final Map<IPredicate, Validity> expliedPredicates);

}