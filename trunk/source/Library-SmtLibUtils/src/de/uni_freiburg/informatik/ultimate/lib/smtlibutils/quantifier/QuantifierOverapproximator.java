/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Expects input in NNF, replaces quantified formulas by "true".
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierOverapproximator extends TermTransformer {

	private final Script mScript;

	private QuantifierOverapproximator(final Script script) {
		mScript = script;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term notTerm = SmtUtils.unzipNot(appTerm);
			if (notTerm != null) {
				if (!SmtUtils.isAtomicFormula(notTerm)) {
					throw new AssertionError("NNF required for sound overapproximation.");
				}
				setResult(term);
				return;
			}
			super.convert(term);
			return;
		} else if (term instanceof QuantifiedFormula) {
			setResult(mScript.term("true"));
			return;
		} else if (term instanceof TermVariable) {
			setResult(term);
			return;
		} else if (term instanceof ConstantTerm) {
			setResult(term);
			return;
		}
		throw new UnsupportedOperationException("Unsupported kind of Term: " + term.getClass().getSimpleName());
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		setResult(SmtUtils.convertApplicationTerm(appTerm, newArgs, mScript));
	}

	public static Term apply(final Script script, final Term term) {
		return new QuantifierOverapproximator(script).transform(term);
	}

}
