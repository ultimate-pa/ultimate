/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.chc.eldarica;

import ap.parser.IFormula;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.terfor.preds.Predicate;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * Backtranslation from eldarica terms and formulas to Ultimate terms.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
class Backtranslator {
	private final Script mScript;
	private final BidirectionalMap<HcPredicateSymbol, Predicate> mPredicateMap;

	Backtranslator(final Script script, final BidirectionalMap<HcPredicateSymbol, Predicate> predicateMap) {
		mScript = script;
		mPredicateMap = predicateMap;
	}

	public HcPredicateSymbol translatePredicate(final Predicate predicate) {
		return mPredicateMap.inverse().get(predicate);
	}

	public Term translateFormula(final IFormula formula) {
		throw new UnsupportedOperationException();
	}

	public Term translateTerm(final ITerm term, final Sort sort) {
		if (!(term instanceof IIntLit)) {
			throw new IllegalArgumentException(term.toString());
		}

		final var value = ((IIntLit) term).value();
		if (!SmtSortUtils.isBoolSort(sort)) {
			// TODO convert
			new ap.types.Sort.MultipleValueBool$();
		}
		return mScript.numeral(value.bigIntValue());
	}
}
