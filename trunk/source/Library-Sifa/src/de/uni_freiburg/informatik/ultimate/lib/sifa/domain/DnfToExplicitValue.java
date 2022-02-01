/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class DnfToExplicitValue extends TermTransformer {

	private final Term mTrue;

	public DnfToExplicitValue(final SymbolicTools tools) {
		mTrue = tools.top().getFormula();
	}

	/**
	 * @param term The disjunct of a DNF
	 */
	@Override
	protected void convert(final Term term) {
		if (term instanceof TermVariable) {
			setResult(term);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm applTerm = (ApplicationTerm) term;
			final String funName = applTerm.getFunction().getName();
			// TODO use a more sophisticated approach which uses all information in (and (= x 1) (= x y))
			// maybe even all information in (and (= x 1) (= x (+ y 2))) (see what simplification are available first)
			if ("=".equals(funName) && hasAtLeastOneConstant(applTerm.getParameters())) {
				setResult(term);
			} else {
				setResult(mTrue);
			}
		} else if (term instanceof LetTerm) {
			throw new UnsupportedOperationException("We were told there are no let terms");
		} else if (term instanceof AnnotatedTerm) {
			convert(((AnnotatedTerm) term).getSubterm());
		} else if (term instanceof QuantifiedFormula) {
			setResult(mTrue);
		} else {
			throw new UnsupportedOperationException("Not yet implemented: " + term.getClass());
		}
	}

	private static boolean hasAtLeastOneConstant(final Term[] parameters) {
		return Arrays.stream(parameters).anyMatch(a -> a instanceof ConstantTerm);
	}
}
