/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.logic.Logics;

public final class ChcCategorizer {
	private ChcCategorizer() {
		// static class cannot be instantiated
	}

	public static ChcCategoryInfo categorize(final Collection<HornClause> clauses, final ManagedScript mgdScript) {
		return new ChcCategoryInfo(getLogics(clauses, mgdScript), hasNonLinearClauses(clauses));
	}

	public static boolean hasNonLinearClauses(final Collection<HornClause> clauses) {
		return clauses.stream().anyMatch(ChcCategorizer::isNonLinear);
	}

	public static boolean isNonLinear(final HornClause clause) {
		return clause.getBodyPredicates().size() >= 2;
	}

	public static Logics getLogics(final Collection<HornClause> clauses, final ManagedScript mgdScript) {
		final TermClassifier termClassifierChcs = new TermClassifier();
		clauses.forEach(chc -> termClassifierChcs.checkTerm(chc.constructFormula(mgdScript, false)));
		final TermClassifier termClassifierConstraints = new TermClassifier();
		clauses.forEach(chc -> termClassifierConstraints.checkTerm(chc.getConstraintFormula()));

		boolean hasArrays = false;
		boolean hasReals = false;
		boolean hasInts = false;
		for (final String osn : termClassifierChcs.getOccuringSortNames()) {
			hasArrays |= osn.contains(SmtSortUtils.ARRAY_SORT);
			hasReals |= osn.contains(SmtSortUtils.REAL_SORT);
			hasInts |= osn.contains(SmtSortUtils.INT_SORT);
		}

		boolean hasArraysInConstraints = false;
		boolean hasRealsInConstraints = false;
		boolean hasIntsInConstraints = false;
		for (final String osn : termClassifierConstraints.getOccuringSortNames()) {
			hasArraysInConstraints |= osn.contains(SmtSortUtils.ARRAY_SORT);
			hasRealsInConstraints |= osn.contains(SmtSortUtils.REAL_SORT);
			hasIntsInConstraints |= osn.contains(SmtSortUtils.INT_SORT);
		}
		assert hasArrays == hasArraysInConstraints;
		assert hasReals == hasRealsInConstraints;
		assert hasInts == hasIntsInConstraints;

		final boolean hasQuantifiersInConstraints = !termClassifierConstraints.getOccuringQuantifiers().isEmpty();

		if (!hasArrays && hasInts && !hasReals && !hasQuantifiersInConstraints) {
			return Logics.QF_LIA;
		}
		if (!hasArrays && !hasInts && hasReals && !hasQuantifiersInConstraints) {
			return Logics.QF_LRA;
		}
		if (hasArrays && hasInts && !hasReals && !hasQuantifiersInConstraints) {
			return Logics.QF_ALIA;
		}
		// not a CHC-comp 2019 logic -- we don't care for more details right now
		return Logics.ALL;
	}
}
