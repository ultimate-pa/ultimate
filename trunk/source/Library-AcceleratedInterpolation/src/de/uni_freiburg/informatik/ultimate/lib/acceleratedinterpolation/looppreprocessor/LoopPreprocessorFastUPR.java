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

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor;

import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;

/**
 * Preprocess a given loop by transforming not supported transitions.
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 *
 * @param <LETTER>
 *            transition type
 */
public class LoopPreprocessorFastUPR<LETTER extends IIcfgTransition<?>> implements ILoopPreprocessor<LETTER> {

	private final ManagedScript mScript;
	private final ILogger mLogger;
	private final IPredicateUnifier mPredUnifier;

	/**
	 * Remove for example modulo operations from a loop, because FastUPR does not support it.
	 *
	 * @param logger
	 * @param script
	 * @param predUnifier
	 */
	public LoopPreprocessorFastUPR(final ILogger logger, final ManagedScript script,
			final IPredicateUnifier predUnifier) {
		mLogger = logger;
		mScript = script;
		mPredUnifier = predUnifier;
	}

	/**
	 * Preprocess a loop to remove unsupported operations, such as modulo
	 */
	@Override
	public UnmodifiableTransFormula preProcessLoop(final UnmodifiableTransFormula loop) {
		final ApplicationTerm loopAppTerm = (ApplicationTerm) loop.getFormula();
		Term preProcessedLoop = loop.getFormula();
		final Term[] parameters = loopAppTerm.getParameters();
		final Deque<Term> stack = new HashDeque<>();
		for (final Term t : parameters) {
			stack.add(t);
		}
		while (!stack.isEmpty()) {
			final Term term = stack.pop();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction() == mScript.getScript().getFunctionSymbol("mod")) {
					// preProcessedLoop = transformModIte(appTerm, loopAppTerm, preProcessedLoop, term);
					preProcessedLoop = transformModQuantification(appTerm, loopAppTerm, term);
					mLogger.debug("Found modulo!");
				} else {
					for (final Term tt : appTerm.getParameters()) {
						stack.add(tt);
					}
				}
			}
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(loop.getInVars(), loop.getOutVars(), true,
				Collections.emptySet(), true, Collections.emptySet(), false);
		for (final TermVariable auxVar : loop.getAuxVars()) {
			tfb.addAuxVar(auxVar);
		}
		tfb.setFormula(preProcessedLoop);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final UnmodifiableTransFormula preProcessedLoopFormula = tfb.finishConstruction(mScript);
		return preProcessedLoopFormula;

	}

	/**
	 * Replace modulo by an existential quantified formula.
	 *
	 * @param appTerm
	 * @param loopAppTerm
	 * @param term
	 * @return
	 */
	private Term transformModQuantification(final ApplicationTerm appTerm, final ApplicationTerm loopAppTerm,
			final Term term) {
		final Term[] moduloParams = appTerm.getParameters();
		ConstantTerm integerLimit = null;
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
		final Term moduloTerm;
		moduloTerm = moduloParams[moduloParams.length - 1 - integerLimitPosition];

		final TermVariable tv = mScript.constructFreshTermVariable("k", mScript.getScript().sort("Int"));
		final Term upperBound = SmtUtils.geq(mScript.getScript(), tv, mScript.getScript().numeral("0"));
		final Term subtraction =
				SmtUtils.minus(mScript.getScript(), moduloTerm, mScript.getScript().term("*", tv, integerLimit));
		final Term subtractionLimit = SmtUtils.greater(mScript.getScript(), integerLimit, subtraction);

		final Map<Term, Term> subMap = new HashMap<>();
		subMap.put(term, moduloTerm);
		Substitution sub = new Substitution(mScript, subMap);
		Term result = sub.transform(loopAppTerm);
		subMap.clear();
		subMap.put(moduloTerm, subtraction);
		sub = new Substitution(mScript, subMap);
		result = sub.transform(result);
		result = SmtUtils.and(mScript.getScript(), upperBound, subtractionLimit, result);
		final TermVariable[] tvs = new TermVariable[1];
		tvs[0] = tv;
		result = mScript.getScript().quantifier(QuantifiedFormula.EXISTS, tvs, result);
		mLogger.debug(result.toStringDirect());
		return result;
	}

	/**
	 * Replace modulo by an if then else clause
	 */
	private Term transformModIte(final ApplicationTerm appTerm, final ApplicationTerm loopAppTerm,
			final Term preProcessedLoopTerm, final Term term) {
		final Term[] moduloParams = appTerm.getParameters();
		ConstantTerm integerLimit = null;
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
		final Term moduloTerm;
		moduloTerm = moduloParams[moduloParams.length - 1 - integerLimitPosition];
		// final Term moduloUpperBound = SmtUtils.greater(mScript.getScript(), moduloTerm, integerLimit);
		final Term moduloTermNewValue = SmtUtils.minus(mScript.getScript(), moduloTerm, integerLimit);
		// final Term equality = mScript.getScript().term("=", moduloTerm, moduloTermNewValue);
		final Term moduloLowerBound = SmtUtils.greater(mScript.getScript(), integerLimit, moduloTerm);
		// moduloUpperBound = SmtUtils.and(mScript.getScript(), moduloUpperBound, equality);
		final Map<Term, Term> subMap = new HashMap<>();
		final Map<Term, Term> subMapAppTerm = new HashMap<>();
		Term appTermNoModulo = null;
		subMap.put(term, moduloTerm);
		subMapAppTerm.put(term, moduloTerm);
		Substitution sub = new Substitution(mScript, subMap);
		Term result = sub.transform(loopAppTerm);
		subMap.clear();
		subMap.put(moduloTerm, moduloTermNewValue);
		sub = new Substitution(mScript, subMap);
		result = sub.transform(result);

		// preProcessedLoop =
		// SmtUtils.and(mScript.getScript(), preProcessedLoop, moduloDisjunctionReplacement);
		final Substitution subAppTerm = new Substitution(mScript, subMapAppTerm);
		appTermNoModulo = subAppTerm.transform(loopAppTerm);
		return mScript.getScript().term("ite", moduloLowerBound, appTermNoModulo, result);
	}

}