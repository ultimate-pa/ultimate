/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * Wrapper for another {@code IVariableProvider} with a different initial state.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class InterferingVariableProvider<STATE extends IAbstractState<STATE>, ACTION>
		implements IVariableProvider<STATE, ACTION> {
	private final IVariableProvider<STATE, ACTION> mUnderlying;
	private final DisjunctiveAbstractState<STATE> mInterferingState;

	public InterferingVariableProvider(final IVariableProvider<STATE, ACTION> underlying,
			final DisjunctiveAbstractState<STATE> interferingState) {
		mUnderlying = underlying;
		mInterferingState = interferingState;
	}

	@Override
	public DisjunctiveAbstractState<STATE> defineInitialVariables(final ACTION current,
			final DisjunctiveAbstractState<STATE> state) {
		return mUnderlying.defineInitialVariables(current, mInterferingState);
	}

	@Override
	public STATE defineVariablesAfter(final ACTION current, final STATE localPreState,
			final STATE hierachicalPreState) {
		return mUnderlying.defineVariablesAfter(current, localPreState, hierachicalPreState);
	}

	@Override
	public STATE createValidPostOpStateAfterLeaving(final ACTION act, final STATE origPreLinState,
			final STATE preHierState) {
		return mUnderlying.createValidPostOpStateAfterLeaving(act, origPreLinState, preHierState);
	}

	@Override
	public STATE createValidPostOpStateBeforeLeaving(final ACTION action, final STATE stateHier) {
		return mUnderlying.createValidPostOpStateBeforeLeaving(action, stateHier);
	}

	@Override
	public IVariableProvider<STATE, ACTION> createNewVariableProvider(final CfgSmtToolkit toolkit) {
		return mUnderlying.createNewVariableProvider(toolkit);
	}

	@Override
	public Set<IProgramVarOrConst> getRequiredVars(final ACTION act) {
		return mUnderlying.getRequiredVars(act);
	}

}
