/*
 * Copyright (C) 2015-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class ArrayDomainPostOperator<STATE extends IAbstractState<STATE>>
		implements IAbstractPostOperator<ArrayDomainState<STATE>, IcfgEdge> {

	private final ArrayDomainToolkit<STATE> mToolkit;
	private final RcfgStatementExtractor mStatementExtractor;
	private final ArrayDomainStatementProcessor<STATE> mStatementProcessor;

	public ArrayDomainPostOperator(final ArrayDomainToolkit<STATE> toolkit) {
		mToolkit = toolkit;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new ArrayDomainStatementProcessor<>(toolkit);
	}

	@Override
	public List<ArrayDomainState<STATE>> apply(final ArrayDomainState<STATE> oldstate, final IcfgEdge transition) {
		assert oldstate != null;
		assert !oldstate.isBottom() : "You should not need to calculate post of a bottom state";
		assert transition != null;
		final IcfgEdge transitionLabel = transition.getLabel();

		if (transitionLabel instanceof Summary) {
			if (!((Summary) transitionLabel).calledProcedureHasImplementation()) {
				// TODO fix WORKAROUND unsoundness for summary code blocks without procedure implementation
				throw new UnsupportedOperationException("Summary for procedure without implementation: "
						+ BoogiePrettyPrinter.print(((Summary) transitionLabel).getCallStatement()));
			}
			return handleReturnTransition(oldstate, oldstate, transitionLabel);
		} else if (transitionLabel instanceof IIcfgInternalTransition<?>) {
			return handleInternalTransition(oldstate, transitionLabel);
		} else if (transitionLabel instanceof Call) {
			return handleCallTransition(oldstate, oldstate, (Call) transitionLabel);
		} else if (transitionLabel instanceof Return) {
			return handleReturnTransition(oldstate, oldstate, transitionLabel);
		} else {
			throw new UnsupportedOperationException("Unknown transition type: " + transitionLabel.getClass());
		}
	}

	@Override
	public List<ArrayDomainState<STATE>> apply(final ArrayDomainState<STATE> stateBeforeLeaving,
			final ArrayDomainState<STATE> stateAfterLeaving, final IcfgEdge transition) {
		assert stateBeforeLeaving != null;
		assert !stateBeforeLeaving.isBottom() : "You should not need to calculate post of a bottom state (BL)";
		assert stateAfterLeaving != null;
		assert !stateAfterLeaving.isBottom() : "You should not need to calculate post of a bottom state (AL)";
		assert transition != null;

		final IcfgEdge transitionLabel = transition.getLabel();

		assert transitionLabel instanceof Call || transitionLabel instanceof Return
				|| transitionLabel instanceof Summary : "Cannot calculate hierachical post for non-hierachical transition";

		if (transitionLabel instanceof Call) {
			final Call call = (Call) transitionLabel;
			return handleCallTransition(stateBeforeLeaving, stateAfterLeaving, call);
		} else if (transitionLabel instanceof Return || transitionLabel instanceof Summary) {
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, transitionLabel);
		} else {
			throw new UnsupportedOperationException(
					"Array domain does not support context switches other than Call and Return (yet)");
		}
	}

	private List<ArrayDomainState<STATE>> handleCallTransition(final ArrayDomainState<STATE> stateBeforeLeaving,
			final ArrayDomainState<STATE> stateAfterLeaving, final Call call) {
		throw new UnsupportedOperationException("Array domain does not support Call yet");
	}

	private List<ArrayDomainState<STATE>> handleReturnTransition(final ArrayDomainState<STATE> oldstate,
			final ArrayDomainState<STATE> oldstate2, final IcfgEdge transitionLabel) {
		throw new UnsupportedOperationException("Array domain does not support Return yet");
	}

	private List<ArrayDomainState<STATE>> handleInternalTransition(final ArrayDomainState<STATE> oldstate,
			final IcfgEdge transition) {
		ArrayDomainState<STATE> currentState = oldstate;
		final List<Statement> statements = mStatementExtractor.process(transition.getLabel());
		for (final Statement s : statements) {
			currentState = mStatementProcessor.process(currentState, s);
		}
		return Collections.singletonList(currentState);
	}

	@Override
	public EvalResult evaluate(final ArrayDomainState<STATE> state, final Term formula, final Script script) {
		// TODO: Optimize for arrays (if needed)
		return mToolkit.evaluate(state.getSubState(), formula, false);
	}
}
