/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 *
 * {@link TermTransformer} that applies
 * {@link SmtUtils#termWithLocalSimplification(Script, String, Term...)} to all sub-terms in
 * order to create a new term in Ultimate normal form.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UnfTransformer extends TermTransformer {

	private final Script mScript;

	public UnfTransformer(final Script script) {
		mScript = script;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (isEqualityOrDisequalityWithMoreThanTwoParams(appTerm)) {
				final Term binarized = SmtUtils.binarize(mScript, appTerm);
				convert(binarized);
				return;
			} else {
				super.convert(term);
			}
		} else if (term instanceof ConstantTerm) {
			final ConstantTerm constTerm = (ConstantTerm) term;
			final Rational rational = SmtUtils.toRational(constTerm);
			final Term normalized = rational.toTerm(term.getSort());
			setResult(normalized);
			return;
		} else {
			super.convert(term);
		}
	}

	private static boolean isEqualityOrDisequalityWithMoreThanTwoParams(final ApplicationTerm appTerm) {
		return (appTerm.getFunction().getName().equals("=") || appTerm.getFunction().getName().equals("distinct"))
				&& appTerm.getParameters().length > 2;
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final FunctionSymbol fun = appTerm.getFunction();
		final Term result = SmtUtils.termWithLocalSimplification(mScript, fun, newArgs);
		setResult(result);
		return;
	}




}
