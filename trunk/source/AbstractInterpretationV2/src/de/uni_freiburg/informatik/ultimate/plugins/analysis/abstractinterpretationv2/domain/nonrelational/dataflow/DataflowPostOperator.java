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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DataflowPostOperator<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractPostOperator<DataflowState<ACTION>, ACTION> {

	@Override
	public List<DataflowState<ACTION>> apply(final DataflowState<ACTION> oldstate, final ACTION transition) {
		final UnmodifiableTransFormula tf = getTransformula(transition);
		if (tf.getOutVars().isEmpty()) {
			return Collections.singletonList(oldstate);
		}

		final Map<IProgramVarOrConst, Set<ACTION>> reach = new HashMap<>(oldstate.getReachingDefinitions());
		final Map<IProgramVarOrConst, Set<IcfgLocation>> noWrite = new HashMap<>(oldstate.getNoWrite());

		// for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
		// reach.put(entry.getKey(), Collections.singleton(transition));
		// }
		final Set<IProgramVarOrConst> defSet = computeDefSetFromTransFormula(tf, oldstate.getVariables());
		final Set<IProgramVarOrConst> nonDefSet = new HashSet<>(oldstate.getVariables());
		nonDefSet.removeAll(defSet);

		for (final IProgramVarOrConst pv : defSet) {
			reach.put(pv, Collections.singleton(transition));
			noWrite.put(pv, new HashSet<>());
		}
		for (final IProgramVarOrConst pv : nonDefSet) {
			Set<IcfgLocation> programPoints = noWrite.get(pv);
			if (programPoints == null) {
				programPoints = new HashSet<>();
				noWrite.put(pv, programPoints);
			}
			programPoints.add(transition.getSource());
		}

		return Collections.singletonList(
				new DataflowState<>(oldstate.getVariables(), oldstate.getDef(), oldstate.getUse(), reach, noWrite));
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

	@Override
	public List<DataflowState<ACTION>> apply(final DataflowState<ACTION> stateBeforeLeaving,
			final DataflowState<ACTION> stateAfterLeaving, final ACTION transition) {
		return null;
	}

	private static Set<IProgramVarOrConst> computeDefSetFromTransFormula(final UnmodifiableTransFormula tf,
			final Set<IProgramVarOrConst> allVariables) {
		// TODO I think we will need something like "constrained vars"
		// i.e. the set of IProgramVars x where invar(x) = outVar(x) and where
		// x is constrained by the formula (i.e. like from an assume statement)

		// for now: rudimentary test if it is an assume -- then return all outvars
		// otherwise return the AssignedVars
		if (tf.getInVars().keySet().equals(tf.getOutVars().keySet())) { // TODO: don't use keySet()
			return allVariables;
		}
		return new HashSet<>(tf.getAssignedVars());
	}

	@Override
	public de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator.EvalResult
			evaluate(final DataflowState<ACTION> state, final Term formula, final Script script) {
		throw new UnsupportedOperationException("Not implemented yet.");
	}
}
