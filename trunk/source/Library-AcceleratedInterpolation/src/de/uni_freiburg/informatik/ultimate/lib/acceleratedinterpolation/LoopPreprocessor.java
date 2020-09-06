/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;

public class LoopPreprocessor<LETTER extends IIcfgTransition<?>> {

	private final ManagedScript mScript;
	private final ILogger mLogger;

	public LoopPreprocessor(final ILogger logger, final ManagedScript script) {
		mLogger = logger;
		mScript = script;
	}

	public UnmodifiableTransFormula preProcessLoopOctagon(final UnmodifiableTransFormula loop) {
		final ApplicationTerm loopAppTerm = (ApplicationTerm) loop.getFormula();
		final Term[] parameters = loopAppTerm.getParameters();
		final Deque<Term> stack = new HashDeque<>();
		final Map<Term, Term> subMap = new HashMap<>();
		for (final Term t : parameters) {
			stack.add(t);
		}
		while (!stack.isEmpty()) {
			final Term term = stack.pop();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction() == mScript.getScript().getFunctionSymbol("mod")) {
					final Term[] moduloParams = appTerm.getParameters();
					ConstantTerm integerLimit = null;
					final Term moduloTerm;
					int integerLimitPosition = -1;
					for (int i = 0; i < moduloParams.length; i++) {
						final Term moduloParam = moduloParams[i];
						if (moduloParam instanceof ConstantTerm) {
							integerLimit = (ConstantTerm) moduloParam;
							integerLimitPosition = i;
						}
					}
					if (integerLimit == null) {
						throw new UnsupportedOperationException("There is no upper integer limit");
					}
					moduloTerm = moduloParams[moduloParams.length - 1 - integerLimitPosition];
					final Term moduloBound = SmtUtils.greater(mScript.getScript(), integerLimit, moduloTerm);
					final Term moduloTermNewValue = SmtUtils.minus(mScript.getScript(), moduloTerm, integerLimit);
					final Term equality = mScript.getScript().term("=", moduloTerm, moduloTermNewValue);
					final Term moduloDisjunctionReplacement = SmtUtils.or(mScript.getScript(), moduloBound, equality);
					subMap.put(appTerm, moduloTerm);
					mLogger.debug("Found modulo!");
				} else {
					for (final Term tt : appTerm.getParameters()) {
						stack.add(tt);
					}
				}
			}
		}
		if (!subMap.isEmpty()) {
			final Substitution sub = new Substitution(mScript, subMap);
			final Term newLoopTerm = sub.transform(loopAppTerm);
			mLogger.debug("Preprocessed Loop");
		}
		return loop;

	}

}