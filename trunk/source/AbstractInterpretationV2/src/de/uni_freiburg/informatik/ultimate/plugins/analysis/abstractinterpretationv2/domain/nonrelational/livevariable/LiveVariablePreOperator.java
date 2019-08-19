/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.livevariable;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class LiveVariablePreOperator<ACTION extends IAction>
		implements IAbstractTransformer<LiveVariableState<ACTION>, ACTION> {

	@Override
	public List<LiveVariableState<ACTION>> apply(final LiveVariableState<ACTION> oldstate, final ACTION transition) {
		final UnmodifiableTransFormula tf = getTransformula(transition);
		final Set<IProgramVarOrConst> gen = new HashSet<>(tf.getInVars().keySet());
		final Set<IProgramVarOrConst> kill = new HashSet<>(tf.getOutVars().keySet());

		final Set<IProgramVarOrConst> newLive =
				DataStructureUtils.union(gen, DataStructureUtils.difference(oldstate.getLiveVariables(), kill));
		return Collections.singletonList(new LiveVariableState<>(newLive));
	}

	private UnmodifiableTransFormula getTransformula(final ACTION transition) {
		if (transition instanceof IInternalAction) {
			return ((IInternalAction) transition).getTransformula();
		} else if (transition instanceof ICallAction) {
			return ((ICallAction) transition).getLocalVarsAssignment();
		} else if (transition instanceof IReturnAction) {
			return ((IReturnAction) transition).getAssignmentOfReturn();
		}
		throw new UnsupportedOperationException("Unknown transition type " + transition.getClass().getSimpleName());
	}
}
