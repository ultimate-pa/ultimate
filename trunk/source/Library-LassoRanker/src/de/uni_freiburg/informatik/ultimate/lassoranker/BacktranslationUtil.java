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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;


/**
 * Translates parts of a NonterminationArgument to assist the generation of
 * instances of NonterminationArgumentResult
 * 
 * @author Jan Leike
 *
 */
public class BacktranslationUtil {
	
	/**
	 * Translate a RankVar into a (Boogie) Expression. The Expression is the
	 * (unique) Expression that represents the definition of the RankVar.
	 */
	private static Expression rankVar2Expression(final Term2Expression term2expression, final RankVar rv) {
		return term2expression.translate(ReplacementVarUtils.getDefinition(rv));
	}
	
	/**
	 * Translate a sequence of mappings from RankVars to Rationals into a 
	 * sequence of mappings from Expressions to Rationals.
	 * The RanksVars are translated into an Expressions that represents the
	 * defining term of the RankVar. The Rationals are are translated to 1 
	 * (true) and 0 (false) if the corresponding RankVar represented a Term
	 * of sort Bool.
	 * Ensures that RankVars that are defined by equivalent terms translated 
	 * to the same Expression object. 
	 */
	public static List<Map<Expression, Rational>> rank2Boogie(
			final Term2Expression term2expression,
			final List<Map<RankVar, Rational>> states) {
		final List<Map<Expression, Rational>> result =
				new ArrayList<Map<Expression, Rational>>(states.size());
		for (final Map<RankVar, Rational> state : states) {
			final Map<Expression, Rational> expression2rational =
					new LinkedHashMap<Expression, Rational>();
			for (final Map.Entry<RankVar, Rational> entry : state.entrySet()) {
				final Term definition = ReplacementVarUtils.getDefinition(entry.getKey());
				final Expression e = term2expression.translate(definition);
				Rational r = entry.getValue();
				// Replace Rational for boolean RankVars
				if (definition.getSort().getName().equals("Bool")) {
					// value >= 1 means true, which is translated to 1,
					// false is translated to 0.
					r = entry.getValue().compareTo(Rational.ONE) == -1 ?
							Rational.ONE : Rational.ZERO;
				}
				assert e != null && r != null;
				expression2rational.put(e, r);
			}
			result.add(expression2rational);
		}
		return result;
	}
}
