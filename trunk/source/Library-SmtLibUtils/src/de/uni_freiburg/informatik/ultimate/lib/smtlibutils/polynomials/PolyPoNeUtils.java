/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.Junction;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolyPoNeUtils {
	final Script mScript;

	private static final boolean DEBUG_CHECK_RESULT = false;

	private PolyPoNeUtils(final Script script) {
		mScript = script;
	}

	public static Term and(final Script script, final List<Term> params) {
		final Term result = new PolyPoNe(script, Junction.AND).and(params);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			final Term inputTerm = SmtUtils.and(script, params);
			SmtUtils.checkLogicalEquivalenceForDebugging(script, result, inputTerm, PolyPoNeUtils.class,
					tolerateUnknown);
		}
		return result;
	}

	public static Term and(final Script script, final Term context, final List<Term> params) {
		final Term result = new PolyPoNeWithContext(script, Junction.AND, new PolyPoNe(script, Junction.AND))
				.and(context, params);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			final Term inputTerm = SmtUtils.and(script, params);
			SmtUtils.checkLogicalEquivalenceForDebugging(script, result, inputTerm, PolyPoNeUtils.class,
					tolerateUnknown);
		}
		return result;
	}

	public static Term or(final Script script, final List<Term> params) {
		final Term result = new PolyPoNe(script, Junction.OR).or(params);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			final Term inputTerm = SmtUtils.or(script, params);
			SmtUtils.checkLogicalEquivalenceForDebugging(script, result, inputTerm, PolyPoNeUtils.class,
					tolerateUnknown);
		}
		return result;
	}

	public static Term or(final Script script, final Term context, final List<Term> params) {
		final Term result = new PolyPoNeWithContext(script, Junction.OR, new PolyPoNe(script, Junction.OR)).or(context,
				params);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			final Term inputTerm = SmtUtils.or(script, params);
			SmtUtils.checkLogicalEquivalenceForDebugging(script, result, inputTerm, PolyPoNeUtils.class,
					tolerateUnknown);
		}
		return result;
	}

}
