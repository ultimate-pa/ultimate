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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.PoormanAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;

public class TermConjunctEvaluator<STATE extends IAbstractState<STATE>> {

	private final ILogger mLogger;
	private final IAbstractDomain<STATE, IcfgEdge> mBackingDomain;
	private final MappedTerm2Expression mMappedTerm2Expression;
	private final Set<TermVariable> mVariableRetainmentSet;
	private final Map<TermVariable, String> mAlternateOldNames;
	private final CodeBlockFactory mCodeBlockFactory;
	private final Function<Collection<STATE>, Collection<STATE>> mPostFunction;
	private final Script mScript;
	private final Map<Term[], CodeBlock> mCachedCodeBlocks;

	public TermConjunctEvaluator(final ILogger logger, final Term term,
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
		mCachedCodeBlocks = new HashMap<>();
		mPostFunction = visit(term);
	}

	public Collection<STATE> computePost(final PoormanAbstractState<STATE> prestate) {
		if (mPostFunction == null) {
			throw new UnsupportedOperationException("No result produced.");
		}
		return mPostFunction.apply(Collections.singletonList(prestate.getBackingState()));
	}

	private Function<Collection<STATE>, Collection<STATE>> visit(final Term term) {
		if (term instanceof ApplicationTerm) {
			return visit((ApplicationTerm) term);
		} else if (term instanceof AnnotatedTerm) {
			return visit((AnnotatedTerm) term);
		} else if (term instanceof LetTerm) {
			return visit((LetTerm) term);
		} else if (term instanceof QuantifiedFormula) {
			return visit((QuantifiedFormula) term);
		} else if (term instanceof TermVariable) {
			return visit((TermVariable) term);
		} else {
			throw new UnsupportedOperationException("Unsupported term type: " + term.getClass().getSimpleName());
		}
	}

	private Function<Collection<STATE>, Collection<STATE>> visit(final TermVariable term) {
		return (prestate) -> {
			return applyPost(prestate, term);
		};
	}

	private Function<Collection<STATE>, Collection<STATE>> visit(final QuantifiedFormula term) {
		throw new UnsupportedOperationException("Quantified formulas cannot be handled right now.");
	}

	private Function<Collection<STATE>, Collection<STATE>> visit(final LetTerm term) {
		throw new UnsupportedOperationException("LetTerm formulas cannot be handled right now.");
	}

	private Function<Collection<STATE>, Collection<STATE>> visit(final AnnotatedTerm term) {
		throw new UnsupportedOperationException("AnnotatedTerm formulas cannot be handled right now.");
	}

	private Function<Collection<STATE>, Collection<STATE>> visit(final ApplicationTerm term) {
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
			return (prestates) -> {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Abstractables:     " + abstractables);
					mLogger.debug("Non-Abstractables: " + nonAbstractables);
				}
				final Collection<STATE> preStatesAfterAbstractables =
						applyPost(prestates, abstractables.toArray(new Term[abstractables.size()]));
				return computeFixpoint(nonAbstractables, preStatesAfterAbstractables);
			};
		} else if (functionName.equals("or")) {
			return (prestates) -> {
				final Set<STATE> returnStates = new HashSet<>();
				for (final Term param : term.getParameters()) {
					returnStates.addAll(visit(param).apply(prestates));
				}
				return returnStates;
			};
		} else if (functionName.equals("not")) {
			assert term.getParameters().length == 1;
			final Term param = term.getParameters()[0];
			if (param instanceof ApplicationTerm) {
				final ApplicationTerm appParam = (ApplicationTerm) param;
				final Term invertedTerm = negateTerm(appParam);
				if (invertedTerm == appParam) {
					// If the term is something like (not (= x y)), compute the post right away and let the domain deal
					// with the negation.
					return (prestates) -> {
						return applyPost(prestates, term);
					};
				}
				return visit(invertedTerm);
			}
		}

		return (prestates) -> {
			return applyPost(prestates, term);
		};
	}

	private Collection<STATE> computeFixpoint(final Collection<Term> nonAbstractables,
			final Collection<STATE> preStates) {
		if (nonAbstractables.isEmpty()) {
			return preStates;
		}

		DisjunctiveAbstractState<STATE> pres = DisjunctiveAbstractState.createDisjunction(preStates);
		int i = 0;
		Set<STATE> result;
		outerloop: while (true) {
			++i;
			// Compute everything for the prestate
			DisjunctiveAbstractState<STATE> abstractableResult = pres;

			for (final Term nonAbstractable : nonAbstractables) {
				abstractableResult = DisjunctiveAbstractState
						.createDisjunction(visit(nonAbstractable).apply(abstractableResult.getStates()));
				if (abstractableResult.isBottom()) {
					// result = abstractableResult.getStates();
					result = Collections.emptySet();
					break outerloop;
				}
			}

			final DisjunctiveAbstractState<STATE> previousPres = pres;
			if (abstractableResult.isSubsetOf(previousPres) != SubsetResult.NONE) {
				result = abstractableResult.getStates();
				break;
			}
			pres = abstractableResult;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Computed fixpoint for " + nonAbstractables.size() + " terms and " + preStates.size()
					+ " states in " + i + " iterations, resulting in " + result.size() + " states");
		}
		return result;
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

	private CodeBlock getCachedCodeBlock(final Term... term) {
		if (term.length == 0) {
			return null;
		}
		final CodeBlock cachedBlock = mCachedCodeBlocks.get(term);
		if (cachedBlock != null) {
			return cachedBlock;
		}

		final AssumeStatement[] assume = AssumptionBuilder.constructBoogieAssumeStatement(mLogger,
				mVariableRetainmentSet, mAlternateOldNames, mMappedTerm2Expression, term);

		final CodeBlock codeBlock = AssumptionBuilder.constructCodeBlock(mCodeBlockFactory, assume);

		mCachedCodeBlocks.put(term, codeBlock);
		return codeBlock;
	}

	private Collection<STATE> applyPost(final Collection<STATE> preStates, final Term... term) {

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("PreStates: " + preStates);
		}

		// If all preStates are bottom, we just return them and do nothing.
		if (preStates.stream().allMatch(state -> state.isBottom())) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("PostStates: " + preStates);
			}
			return preStates;
		}

		final CodeBlock codeBlock = getCachedCodeBlock(term);
		if (codeBlock == null) {
			return preStates;
		}
		final Set<STATE> returnStates = new HashSet<>();
		for (final STATE state : preStates) {
			// Skip bottom states
			if (state.isBottom()) {
				continue;
			}
			returnStates.addAll(mBackingDomain.getPostOperator().apply(state, codeBlock));
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("PostStates: " + returnStates);
		}

		return returnStates;
	}
}
