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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;

public class AbsIntPredicateInterpolantSequenceWeakener<STATE extends IAbstractState<STATE, VARDECL>, VARDECL, LETTER extends IIcfgTransition<?>>
		extends InterpolantSequenceWeakener<IHoareTripleChecker, AbsIntPredicate<STATE, VARDECL>, LETTER> {

	public AbsIntPredicateInterpolantSequenceWeakener(final ILogger logger, final IHoareTripleChecker htc,
			final List<AbsIntPredicate<STATE, VARDECL>> predicates, final List<LETTER> trace,
			final AbsIntPredicate<STATE, VARDECL> precondition, final AbsIntPredicate<STATE, VARDECL> postcondition) {
		super(logger, htc, predicates, trace, precondition, postcondition);
	}

	@Override
	protected AbsIntPredicate<STATE, VARDECL> refinePreState(final AbsIntPredicate<STATE, VARDECL> preState,
			final LETTER transition, final AbsIntPredicate<STATE, VARDECL> postState) {

		// States consists of pre = <s1 OR s2 OR s3 OR ...>, post = <p1 OR p2 OR p3 OR ...>
		for (final STATE s : preState.getAbstractStates()) {

		}

		return preState;
	}

}
