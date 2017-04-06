/*
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.weakener;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class AbsIntPredicateInterpolantSequenceWeakener<STATE extends IAbstractState<STATE, VARDECL>, VARDECL, LETTER extends IIcfgTransition<?>>
		extends InterpolantSequenceWeakener<IHoareTripleChecker, AbsIntPredicate<STATE, VARDECL>, LETTER> {

	public AbsIntPredicateInterpolantSequenceWeakener(final ILogger logger, final IHoareTripleChecker htc,
			final List<AbsIntPredicate<STATE, VARDECL>> predicates, final List<LETTER> trace,
			final AbsIntPredicate<STATE, VARDECL> precondition, final AbsIntPredicate<STATE, VARDECL> postcondition,
			final Script script, final BasicPredicateFactory predicateFactory) {
		super(logger, htc, predicates, trace, precondition, postcondition, script, predicateFactory);
	}

	@Override
	protected AbsIntPredicate<STATE, VARDECL> refinePreState(final AbsIntPredicate<STATE, VARDECL> preState,
			final LETTER transition, final AbsIntPredicate<STATE, VARDECL> postState) {

		// Collect all variables occurring in the invars
		final Set<IProgramVar> varsToKeep = transition.getTransformula().getInVars().keySet();

		final Set<STATE> newMultiState = new HashSet<>();

		for (final STATE s : preState.getAbstractStates()) {
			final Set<VARDECL> varsToRemove =
					s.getVariables().stream().filter(var -> !varsToKeep.contains(var)).collect(Collectors.toSet());

			newMultiState.add(s.removeVariables(varsToRemove));
		}

		final Set<Term> terms = newMultiState.stream().map(s -> s.getTerm(mScript)).collect(Collectors.toSet());
		final IPredicate disjunction = mPredicateFactory.newPredicate(SmtUtils.or(mScript, terms));

		final AbsIntPredicate<STATE, VARDECL> newPreState = new AbsIntPredicate<>(disjunction, newMultiState);

		final Validity result;

		if (transition instanceof IInternalAction) {
			result = mHtc.checkInternal(newPreState, (IInternalAction) transition, postState);
		} else if (transition instanceof ICallAction) {
			result = mHtc.checkCall(newPreState, (ICallAction) transition, postState);
		} else if (transition instanceof IReturnAction) {
			final AbsIntPredicate<STATE, VARDECL> hierarchicalPre = mHierarchicalPreStates.get(preState);
			assert hierarchicalPre != null;
			result = mHtc.checkReturn(newPreState, hierarchicalPre, (IReturnAction) transition, postState);
		} else {
			throw new IllegalStateException(
					"Transition type " + transition.getClass().getSimpleName() + " not supported.");
		}

		if (result == Validity.VALID) {
			mLogger.debug("Result of weakening: Number of variables in state before: " + preState.getVars().size()
					+ ", Number of variables after: " + newPreState.getVars().size());
			return newPreState;
		}

		mLogger.debug("Unable to weaken prestate. Returning old prestate.");
		return preState;
	}

}
