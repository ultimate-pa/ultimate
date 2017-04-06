/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;

/**
 * The {@link DummyInterpolantSequenceWeakener} does nothing. It just returns the sequence of predicates it was given.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class DummyInterpolantSequenceWeakener<STATE extends IAbstractState<STATE, VARDECL>, VARDECL, LETTER extends IIcfgTransition<?>>
		extends InterpolantSequenceWeakener<IHoareTripleChecker, AbsIntPredicate<STATE, VARDECL>, LETTER> {

	/**
	 * Default constructor.
	 *
	 * @param logger
	 * @param htc
	 * @param predicates
	 * @param trace
	 * @param precondition
	 * @param postcondition
	 */
	public DummyInterpolantSequenceWeakener(final ILogger logger, final IHoareTripleChecker htc,
			final List<AbsIntPredicate<STATE, VARDECL>> predicates, final List<LETTER> trace,
			final AbsIntPredicate<STATE, VARDECL> precondition, final AbsIntPredicate<STATE, VARDECL> postcondition) {
		super(logger, htc, predicates, trace, precondition, postcondition);
	}

	@Override
	protected List<AbsIntPredicate<STATE, VARDECL>>
			generateResult(final List<AbsIntPredicate<STATE, VARDECL>> predicates, final List<LETTER> list) {
		return predicates;
	}

	@Override
	protected AbsIntPredicate<STATE, VARDECL> refinePreState(final AbsIntPredicate<STATE, VARDECL> preState,
			final LETTER transition, final AbsIntPredicate<STATE, VARDECL> postState) {
		// Always return the current prestate. The dummy weakener is just supposed to return the original list of
		// predicates and do nothing with them.
		return preState;
	}
}
