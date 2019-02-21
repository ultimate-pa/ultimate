/*
 * Copyright (C) 2019 Matthias Heizmann(heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 *
 * @author Matthias Heizmann(heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 *
 */
public class SmtTestUtils {

	private SmtTestUtils() {
		// do not instantiate
	}

	/**
	 * Returns true iff the solver (script) is able to prove that the terms t1 and
	 * t2 are logically equivalent.
	 */
	public static boolean areEquivalent(final Script script, final Term t1, final Term t2) {
		return Util.checkSat(script, script.term("distinct", t1, t2)) == LBool.UNSAT;
	}

	public static boolean areLogicallyEquivalent(final Script script, final Term formula1, final String formula2AsString) {
		final Term formula2AsTerm = TermParseUtils.parseTerm(script, formula2AsString);
		return areEquivalent(script, formula1, formula2AsTerm);
	}

	public static boolean isValid(final Script script, final String formulaAsString) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(script, formulaAsString);
		return areEquivalent(script, script.term("true"), formulaAsTerm);
	}

	public static boolean areSyntacticallyEquivalent(final Script script, final Term formula1, final String formula2AsString) {
		final Term formula2AsTerm = TermParseUtils.parseTerm(script, formula2AsString);
		return formula1 == formula2AsTerm;
	}

	public static boolean isSyntacticallyEquivalentToTrue(final Term term) {
		return SmtUtils.isTrue(term);
	}

}
