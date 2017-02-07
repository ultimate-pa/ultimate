/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational;

import java.nio.channels.UnsupportedAddressTypeException;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public abstract class NonrelationalPostOperator<STATE extends NonrelationalState<STATE, V, IProgramVarOrConst>, ACTION, V extends INonrelationalValue<V>>
		implements IAbstractPostOperator<STATE, ACTION, IProgramVarOrConst> {
	
	private final ILogger mLogger;
	
	protected NonrelationalPostOperator(final ILogger logger) {
		mLogger = logger;
	}
	
	@Override
	public List<STATE> apply(final STATE oldstate, final ACTION transition) {
		assert oldstate != null;
		assert !oldstate.isBottom() : "Trying to compute post for a bottom state.";
		assert transition != null;
		
		// TODO fix WORKAROUND unsoundness for summary code blocks without procedure implementation
		if (transition instanceof Summary && !((Summary) transition).calledProcedureHasImplementation()) {
			throw new UnsupportedOperationException("Summary for procedure without implementation");
		}
		
		final UnmodifiableTransFormula transformula;
		
		if (transition instanceof CodeBlock) {
			transformula = ((CodeBlock) transition).getTransformula();
		} else if (transition instanceof IcfgEdge) {
			transformula = ((IcfgEdge) transition).getTransformula();
		} else {
			throw new UnsupportedOperationException(
					"Unknown instance of transition: " + transition.getClass().getSimpleName());
		}

		final Term term = transformula.getFormula();
		
		final NonrelationalTermProcessor termWalker = new NonrelationalTermProcessor(mLogger);
		termWalker.process(term);
		
		final List<STATE> currentStates = new ArrayList<>();
		currentStates.add(oldstate);
		
		if (true) {
			throw new UnsupportedOperationException("Not implemented");
		}
		
		// TODO
		
		return currentStates;
	}
	
	@Override
	public List<STATE> apply(final STATE stateBeforeLeaving, final STATE stateAfterLeaving, final ACTION transition) {
		assert transition instanceof Call || transition instanceof Return
				|| transition instanceof Summary : "Cannot calculate hierachical post for non-hierachical transition";

		if (transition instanceof Call) {
			final Call call = (Call) transition;
			return handleCallTransition(stateBeforeLeaving, stateAfterLeaving, call);
		} else if (transition instanceof Return) {
			final Return ret = (Return) transition;
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, ret.getCallStatement());
		} else if (transition instanceof Summary) {
			final Summary summary = (Summary) transition;
			return handleReturnTransition(stateBeforeLeaving, stateAfterLeaving, summary.getCallStatement());
		} else {
			throw new UnsupportedOperationException(
					"Nonrelational domains do not support context switches other than Call and Return (yet)");
		}
	}
	
	private List<STATE> handleCallTransition(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final Call call) {
		final List<STATE> returnList = new ArrayList<>();
		final CallStatement callStatement = call.getCallStatement();
		final Expression[] args = callStatement.getArguments();

		// If there are no arguments, we don't need to rewrite states.
		if (args.length == 0) {
			returnList.add(stateAfterLeaving);
			return returnList;
		}

		throw new UnsupportedAddressTypeException();
	}

	private List<STATE> handleReturnTransition(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final CallStatement callStatement) {
		throw new UnsupportedOperationException();
	}
	
}
