/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class IcfgProgramExecutionBuilder<L extends IAction> {

	private final ModifiableGlobalsTable mModifiableGlobalVariableManager;
	private final NestedWord<L> mTrace;
	private final Map<IProgramVar, Map<Integer, Term>> mVar2Pos2Value;
	private final RelevantVariables<L> mRelevantVariables;
	private IcfgProgramExecution<L> mIcfgProgramExecution;
	private final Map<TermVariable, Boolean>[] mBranchEncoders;

	@SuppressWarnings("unchecked")
	public IcfgProgramExecutionBuilder(final ModifiableGlobalsTable modifiableGlobalsTable, final NestedWord<L> trace,
			final RelevantVariables<L> relevantVariables) {
		super();
		mModifiableGlobalVariableManager = modifiableGlobalsTable;
		mTrace = trace;
		mVar2Pos2Value = new HashMap<>();
		mRelevantVariables = relevantVariables;
		mBranchEncoders = new Map[mTrace.length()];
		mIcfgProgramExecution = null;
	}

	public IcfgProgramExecution<L> getIcfgProgramExecution() {
		if (mIcfgProgramExecution == null) {
			mIcfgProgramExecution = computeIcfgProgramExecution();
		}
		return mIcfgProgramExecution;
	}

	private boolean isReAssigned(final IProgramVar bv, final int position) {
		boolean result;
		if (mTrace.isInternalPosition(position) || mTrace.isReturnPosition(position)) {
			final UnmodifiableTransFormula tf = mTrace.getSymbol(position).getTransformula();
			result = tf.getAssignedVars().contains(bv);
		} else if (mTrace.isCallPosition(position)) {
			final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) mTrace.getSymbol(position);
			final String callee = call.getSucceedingProcedure();
			if (bv.isGlobal()) {
				final Set<IProgramNonOldVar> modGlobals =
						mModifiableGlobalVariableManager.getModifiedBoogieVars(callee);
				if (bv instanceof IProgramNonOldVar) {
					result = modGlobals.contains(bv);
				} else if (bv instanceof IProgramOldVar) {
					result = modGlobals.contains(((IProgramOldVar) bv).getNonOldVar());
				} else {
					throw new AssertionError("unknown var");
				}
			} else {
				result = callee.equals(bv.getProcedure());
			}
		} else {
			throw new AssertionError();
		}
		return result;
	}

	void addValueAtVarAssignmentPosition(final IProgramVar bv, final int index, final Term value) {
		assert index >= -1;
		assert index == -1 || isReAssigned(bv, index) : "oldVar in procedure where it is not modified?";
		final Map<Integer, Term> pos2value = mVar2Pos2Value.computeIfAbsent(bv, a -> new HashMap<>());
		assert !pos2value.containsKey(index);
		pos2value.put(index, value);
	}

	public void setBranchEncoders(final int i, final Map<TermVariable, Boolean> beMapping) {
		mBranchEncoders[i] = beMapping;
	}

	private int indexWhereVarWasAssignedTheLastTime(final IProgramVar bv, final int pos) {
		assert pos >= -1;
		if (pos == -1) {
			return -1;
		}
		if (isReAssigned(bv, pos)) {
			return pos;
		}
		if (mTrace.isInternalPosition(pos) || mTrace.isCallPosition(pos)) {
			return indexWhereVarWasAssignedTheLastTime(bv, pos - 1);
		} else if (mTrace.isReturnPosition(pos)) {
			if (bv.isGlobal() && !bv.isOldvar()) {
				return indexWhereVarWasAssignedTheLastTime(bv, pos - 1);
			}
			final int callPos = mTrace.getCallPosition(pos);
			return indexWhereVarWasAssignedTheLastTime(bv, callPos - 1);
		} else {
			throw new AssertionError();
		}

	}

	public Map<IProgramVar, Term> varValAtPos(final int position) {
		final Map<IProgramVar, Term> result = new HashMap<>();
		final Set<IProgramVar> vars = mRelevantVariables.getForwardRelevantVariables()[position + 1];
		for (final IProgramVar bv : vars) {
			if (SmtUtils.isSortForWhichWeCanGetValues(bv.getTermVariable().getSort())) {
				final int assignPos = indexWhereVarWasAssignedTheLastTime(bv, position);
				final Term value = mVar2Pos2Value.get(bv).get(assignPos);
				if (value != null) {
					result.put(bv, value);
				}
			}
		}
		return result;
	}

	private IcfgProgramExecution<L> computeIcfgProgramExecution() {
		final Map<Integer, ProgramState<Term>> partialProgramStateMapping = new HashMap<>();
		for (int i = 0; i < mTrace.length(); i++) {
			final Map<IProgramVar, Term> varValAtPos = varValAtPos(i);
			final Map<Term, Collection<Term>> variable2Values = new HashMap<>();
			for (final Entry<IProgramVar, Term> entry : varValAtPos.entrySet()) {
				final IProgramVar bv = entry.getKey();
				variable2Values.put(bv.getTermVariable(), Collections.singleton(entry.getValue()));
			}
			final ProgramState<Term> pps = new ProgramState<>(variable2Values, Term.class);
			partialProgramStateMapping.put(i, pps);
		}
		return IcfgProgramExecution.create(mTrace.asList().stream().collect(Collectors.toList()),
				partialProgramStateMapping, mBranchEncoders);
	}

}
