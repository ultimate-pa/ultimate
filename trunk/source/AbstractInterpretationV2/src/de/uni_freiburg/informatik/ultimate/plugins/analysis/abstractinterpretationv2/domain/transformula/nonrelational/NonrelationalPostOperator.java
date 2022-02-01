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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational;

import java.nio.channels.UnsupportedAddressTypeException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState.VariableType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public abstract class NonrelationalPostOperator<STATE extends NonrelationalState<STATE, V>, ACTION, V extends INonrelationalValue<V>>
		implements IAbstractPostOperator<STATE, ACTION> {

	private final ILogger mLogger;
	private final NonrelationalTermProcessor<V, STATE> mTermProcessor;
	private final Supplier<STATE> mTopStateSupplier;

	protected NonrelationalPostOperator(final ILogger logger, final NonrelationalTermProcessor<V, STATE> termProcessor,
			final Supplier<STATE> topStateSupplier) {
		mLogger = logger;
		mTermProcessor = termProcessor;
		mTopStateSupplier = topStateSupplier;
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

		final Map<String, IProgramVarOrConst> identifierMap = createIdentifierMap(oldstate, transformula);
		final STATE newPreState = createNewPreState(oldstate, transformula, identifierMap);

		final List<STATE> result = mTermProcessor.process(term, newPreState);

		return createPostStates(result, oldstate, transformula, identifierMap);
	}

	private Map<String, IProgramVarOrConst> createIdentifierMap(final STATE oldState,
			final UnmodifiableTransFormula transformula) {
		final Map<String, IProgramVarOrConst> identifierMap = new HashMap<>();

		// InVars
		for (final Entry<IProgramVar, TermVariable> entry : transformula.getInVars().entrySet()) {
			final IProgramVarOrConst programVar = entry.getKey();
			final TermVariable termVar = entry.getValue();

			final IProgramVarOrConst newVar =
					new DummyProgramVar(termVar.getName(), programVar.isGlobal(), programVar.getTerm());

			assert !identifierMap.containsKey(newVar.getGloballyUniqueId());
			identifierMap.put(newVar.getGloballyUniqueId(), newVar);
		}

		// OutVars
		for (final Entry<IProgramVar, TermVariable> entry : transformula.getOutVars().entrySet()) {
			final IProgramVarOrConst programVar = entry.getKey();
			final TermVariable termVar = entry.getValue();

			// Create a dummy var for evaluation if not already in the state
			if (!identifierMap.containsKey(termVar.getName())) {
				final IProgramVarOrConst newVar =
						new DummyProgramVar(termVar.getName(), programVar.isGlobal(), programVar.getTerm());

				identifierMap.put(newVar.getGloballyUniqueId(), newVar);
			}
		}

		// AuxVars
		for (final TermVariable var : transformula.getAuxVars()) {
			assert !identifierMap.containsKey(var.getName());

			// Create a dummy var
			final IProgramVarOrConst newVar = new DummyProgramVar(var.getName(), false, null);

			identifierMap.put(newVar.getGloballyUniqueId(), newVar);
		}

		return identifierMap;
	}

	private STATE createNewPreState(final STATE oldState, final UnmodifiableTransFormula transformula,
			final Map<String, IProgramVarOrConst> identifierMap) {
		STATE newPreState = mTopStateSupplier.get();

		// Add inVars
		for (final Entry<IProgramVar, TermVariable> entry : transformula.getInVars().entrySet()) {
			final IProgramVarOrConst programVar = entry.getKey();
			final TermVariable termVar = entry.getValue();

			assert identifierMap.containsKey(termVar.getName());

			// TODO: Collect all values at once! Don't use copy of states as this may be too slow!
			final IProgramVarOrConst var = identifierMap.get(termVar.getName());
			newPreState = newPreState.addVariable(var);

			// Values
			final VariableType type = oldState.getVariableType(programVar);
			switch (type) {
			case VARIABLE:
				newPreState = newPreState.setValue(var, oldState.getValue(programVar));
				break;
			case BOOLEAN:
				newPreState = newPreState.setBooleanValue(var, oldState.getBooleanValue(programVar));
				break;
			case ARRAY:
				throw new UnsupportedOperationException("Arrays are not supported at this point.");
			}
		}

		// Add outVars
		for (final TermVariable termVar : transformula.getOutVars().values()) {
			assert identifierMap.containsKey(termVar.getName());
			final IProgramVarOrConst var = identifierMap.get(termVar.getName());
			if (!newPreState.containsVariable(var)) {
				newPreState = newPreState.addVariable(var);
			}
		}

		// Add the auxvars
		for (final TermVariable var : transformula.getAuxVars()) {
			assert identifierMap.containsKey(var.getName());
			final IProgramVarOrConst newVar = identifierMap.get(var.getName());
			newPreState = newPreState.addVariable(newVar);
		}

		return newPreState;
	}

	private List<STATE> createPostStates(final List<STATE> processResult, final STATE oldState,
			final UnmodifiableTransFormula transformula, final Map<String, IProgramVarOrConst> identifierMap) {
		assert processResult != null;
		assert processResult.size() > 0;
		assert oldState != null;
		assert transformula != null;

		final List<STATE> returnList = new ArrayList<>();

		for (final STATE result : processResult) {
			STATE newPostState = oldState;

			// OutVars handling
			for (final Entry<IProgramVar, TermVariable> entry : transformula.getOutVars().entrySet()) {
				final IProgramVar originalVar = entry.getKey();
				final TermVariable termVar = entry.getValue();

				assert oldState.containsVariable(originalVar);
				assert identifierMap.containsKey(termVar.getName());

				final IProgramVarOrConst termStateVar = identifierMap.get(termVar.getName());

				assert result.containsVariable(termStateVar);

				final VariableType type = oldState.getVariableType(originalVar);
				assert type.equals(result.getVariableType(termStateVar));

				switch (type) {
				case VARIABLE:
					newPostState = newPostState.setValue(originalVar, result.getValue(termStateVar));
					break;
				case BOOLEAN:
					newPostState = newPostState.setBooleanValue(originalVar, result.getBooleanValue(termStateVar));
					break;
				case ARRAY:
					throw new UnsupportedOperationException("Arrays are not supported at this point.");
				}
			}

			returnList.add(newPostState);
		}

		return returnList;
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

	private static final class DummyProgramVar implements IProgramVarOrConst {
		private static final long serialVersionUID = 1L;

		private final String mName;
		private final boolean mIsGlobal;
		private final Term mTerm;

		protected DummyProgramVar(final String name, final boolean isGlobal, final Term term) {
			mName = name;
			mIsGlobal = isGlobal;
			mTerm = term;
		}

		@Override
		public String getGloballyUniqueId() {
			return mName;
		}

		@Override
		public boolean isGlobal() {
			return mIsGlobal;
		}

		@Override
		public Term getTerm() {
			return mTerm;
		}

		@Override
		public String toString() {
			return mName;
		}
	}

}
