/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.PoormanAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;

public class TermConjunctEvaluator<STATE extends IAbstractState<STATE>> {

	private final ILogger mLogger;
	IAbstractDomain<STATE, IcfgEdge> mBackingDomain;
	private final MappedTerm2Expression mMappedTerm2Expression;
	private final Set<TermVariable> mVariableRetainmentSet;
	private final Map<TermVariable, String> mAlternateOldNames;
	private final CodeBlockFactory mCodeBlockFactory;
	private final List<STATE> mResult;
	private final Script mScript;

	public TermConjunctEvaluator(final ILogger logger, final PoormanAbstractState<STATE> prestate, final Term term,
			final IAbstractDomain<STATE, IcfgEdge> backingDomain, final Set<TermVariable> variableRetainmentSet,
			final Map<TermVariable, String> alternateOldNames, final MappedTerm2Expression mappedTerm2Expression,
			final CodeBlockFactory codeBlockFactory, final Script script) {
		mLogger = logger;
		mBackingDomain = backingDomain;
		mVariableRetainmentSet = variableRetainmentSet;
		mAlternateOldNames = alternateOldNames;
		mMappedTerm2Expression = mappedTerm2Expression;
		mCodeBlockFactory = codeBlockFactory;
		mScript = script;
		mResult = visit(term, Collections.singletonList(prestate.getBackingState()));
	}

	public List<STATE> getResult() {
		if (mResult == null) {
			throw new UnsupportedOperationException("No result produced.");
		}
		return mResult;
	}

	private List<STATE> visit(final Term term, final List<STATE> prestates) {
		if (term instanceof ApplicationTerm) {
			return visit((ApplicationTerm) term, prestates);
		} else if (term instanceof AnnotatedTerm) {
			return visit((AnnotatedTerm) term, prestates);
		} else if (term instanceof LetTerm) {
			return visit((LetTerm) term, prestates);
		} else if (term instanceof QuantifiedFormula) {
			return visit((QuantifiedFormula) term, prestates);
		} else if (term instanceof TermVariable) {
			return visit((TermVariable) term, prestates);
		} else {
			throw new UnsupportedOperationException("Unsupported term type: " + term.getClass().getSimpleName());
		}
	}

	private List<STATE> visit(final TermVariable term, final List<STATE> prestates) {
		return applyPost(prestates, term);
	}

	private List<STATE> visit(final QuantifiedFormula term, final List<STATE> prestates) {
		throw new UnsupportedOperationException("Quantified formulas cannot be handled right now.");
	}

	private List<STATE> visit(final LetTerm term, final List<STATE> prestates) {
		throw new UnsupportedOperationException("LetTerm formulas cannot be handled right now.");
	}

	private List<STATE> visit(final AnnotatedTerm term, final List<STATE> prestates) {
		throw new UnsupportedOperationException("AnnotatedTerm formulas cannot be handled right now.");
	}

	private List<STATE> visit(final ApplicationTerm term, final List<STATE> prestates) {
		final String functionName = term.getFunction().getName();

		if (functionName.equals("and")) {
			final List<Term> abstractables = new ArrayList<>();
			final List<Term> nonAbstractables = new ArrayList<>();
			for (final Term param : term.getParameters()) {
				if (mBackingDomain.isAbstractable(param)) {
					abstractables.add(param);
				} else {
					nonAbstractables.add(param);
				}
			}
			mLogger.debug("Abstractables:     " + abstractables);
			mLogger.debug("Non-Abstractables: " + nonAbstractables);
			final List<STATE> preStatesAfterAbstractables =
					applyPost(prestates, abstractables.toArray(new Term[abstractables.size()]));
			return computeFixpoint(nonAbstractables, preStatesAfterAbstractables);
		} else if (functionName.equals("or")) {
			final List<STATE> returnStates = new ArrayList<>();
			for (final Term param : term.getParameters()) {
				returnStates.addAll(visit(param, prestates));
			}
			return returnStates;
		} else if (functionName.equals("not")) {
			assert term.getParameters().length == 1;
			final Term param = term.getParameters()[0];
			if (param instanceof ApplicationTerm) {
				final ApplicationTerm appParam = (ApplicationTerm) param;
				final Term invertedTerm = negateTerm(appParam);
				if (invertedTerm == appParam) {
					// If the term is something like (not (= x y)), compute the post right away and let the domain deal
					// with the negation.
					return applyPost(prestates, term);
				}
				return visit(invertedTerm, prestates);
			}
		}

		return applyPost(prestates, term);
	}

	private List<STATE> computeFixpoint(final List<Term> nonAbstractables, final List<STATE> preStates) {
		if (nonAbstractables.isEmpty()) {
			return preStates;
		}

		List<STATE> pres = preStates;
		while (true) {
			mLogger.debug("Beginning new fixpoint iteration of assumes...");
			// Compute everything for the prestate
			List<STATE> abstractableResult = pres;
			for (final Term nonAbstractable : nonAbstractables) {
				abstractableResult = visit(nonAbstractable, abstractableResult);
				if (abstractableResult.stream().allMatch(state -> state.isBottom())) {
					return abstractableResult;
				}
			}

			final List<STATE> previousPres = pres;
			// If for all computed post states there is one state in the prestates which covers the post state, we have
			// found a fixpoint and may return.
			if (abstractableResult.stream().allMatch(
					result -> previousPres.stream().anyMatch(prev -> result.isSubsetOf(prev) != SubsetResult.NONE
							&& prev.isSubsetOf(result) != SubsetResult.NONE))) {
				return abstractableResult;
			}
			pres = abstractableResult;
		}
	}

	private Term negateTerm(final ApplicationTerm term) {
		// TODO: Use TermTransformer

		final String function = term.getFunction().getName();
		String newFunction;

		switch (function) {
		case "and":
			newFunction = "or";
			break;
		case "or":
			newFunction = "and";
			break;
		case ">=":
			assert term.getParameters().length == 2;
			return mScript.term("<", term.getParameters());
		case ">":
			assert term.getParameters().length == 2;
			return mScript.term("<=", term.getParameters());
		case "<=":
			assert term.getParameters().length == 2;
			return mScript.term(">", term.getParameters());
		case "<":
			assert term.getParameters().length == 2;
			return mScript.term(">=", term.getParameters());
		case "not":
			assert term.getParameters().length == 1;
			return term.getParameters()[0];
		case "=":
			return term;
		case "select":
			return mScript.term("=", term, mScript.term("false"));
		case "store":
			// TODO: Handle this as well, maybe.
		default:
			throw new UnsupportedOperationException("Unhandled function for negation: " + function);
		}

		final List<Term> negatedParams = Arrays.stream(term.getParameters()).map(param -> mScript.term("not", param))
				.collect(Collectors.toList());
		final Term[] negatedParamsArray = negatedParams.toArray(new Term[negatedParams.size()]);
		return mScript.term(newFunction, negatedParamsArray);
	}

	private List<STATE> applyPost(final List<STATE> preStates, final Term... term) {
		if (term.length == 0) {
			return preStates;
		}

		final List<STATE> returnStates = new ArrayList<>();

		final AssumeStatement[] assume = AssumptionBuilder.constructBoogieAssumeStatement(mLogger,
				mVariableRetainmentSet, mAlternateOldNames, mMappedTerm2Expression, term);

		mLogger.debug("PreStates: " + preStates);

		// If all preStates are bottom, we just return them and do nothing.
		if (preStates.stream().allMatch(state -> state.isBottom())) {
			mLogger.debug("PostStates: " + preStates);
			return preStates;
		}

		for (final STATE state : preStates) {
			// Skip bottom states
			if (state.isBottom()) {
				continue;
			}
			final CodeBlock codeBlock = AssumptionBuilder.constructCodeBlock(mCodeBlockFactory, assume);
			returnStates.addAll(mBackingDomain.getPostOperator().apply(state, codeBlock));
		}

		mLogger.debug("PostStates: " + returnStates);

		return returnStates;
	}
}
