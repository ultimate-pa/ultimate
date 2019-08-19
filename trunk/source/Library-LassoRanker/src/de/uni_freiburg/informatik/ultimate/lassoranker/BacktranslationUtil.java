/*
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Translates parts of a NonterminationArgument to assist the generation of instances of NonterminationArgumentResult
 *
 * @author Jan Leike
 *
 */
public final class BacktranslationUtil {

	private BacktranslationUtil() {
		// utility class
	}

	/**
	 * Translate a sequence of mappings whose domain are IProgramVars that can also be ReplacementVars into a sequence
	 * of mappings whose domain are Terms. The ReplacementVars are translated into Term that represents the defining
	 * term of the ReplacementVars. The Rationals, which are the values of the mappings are are translated to 1 (true)
	 * and 0 (false) if the corresponding RankVar represented a Term of sort Bool.
	 */
	public static List<Map<Term, Rational>> rank2Rcfg(final List<Map<IProgramVar, Rational>> states) {
		final List<Map<Term, Rational>> result = new ArrayList<>(states.size());
		for (final Map<IProgramVar, Rational> state : states) {
			final Map<Term, Rational> term2rational = new LinkedHashMap<>();
			for (final Map.Entry<IProgramVar, Rational> entry : state.entrySet()) {
				final Term definition = ReplacementVarUtils.getDefinition(entry.getKey());
				Rational r = entry.getValue();
				// Replace Rational for boolean RankVars
				if (SmtSortUtils.isBoolSort(definition.getSort())) {
					// value >= 1 means true, which is translated to 1,
					// false is translated to 0.
					r = entry.getValue().compareTo(Rational.ONE) < 0 ? Rational.ONE : Rational.ZERO;
				}
				assert r != null;
				term2rational.put(definition, r);
			}
			result.add(term2rational);
		}
		return result;
	}
}
