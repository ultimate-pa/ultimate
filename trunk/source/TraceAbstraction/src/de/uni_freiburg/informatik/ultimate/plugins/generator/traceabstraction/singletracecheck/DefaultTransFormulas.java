/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.OldVarsAssignmentCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class DefaultTransFormulas extends NestedFormulas<UnmodifiableTransFormula, IPredicate> {

	private final OldVarsAssignmentCache mModifiableGlobalVariableManager;
	private final boolean mWithBranchEncoders;

	public DefaultTransFormulas(final NestedWord<? extends IAction> nestedWord, final IPredicate precondition,
			final IPredicate postcondition, final SortedMap<Integer, IPredicate> pendingContexts,
			final OldVarsAssignmentCache oldVarsAssignmentCache, final boolean withBranchEncoders) {
		super(nestedWord, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		mModifiableGlobalVariableManager = oldVarsAssignmentCache;
		mWithBranchEncoders = withBranchEncoders;
	}

	public OldVarsAssignmentCache getModifiableGlobalVariableManager() {
		return mModifiableGlobalVariableManager;
	}

	public boolean hasBranchEncoders() {
		return mWithBranchEncoders;
	}

	@Override
	protected UnmodifiableTransFormula getFormulaFromValidNonCallPos(final int i) {
		if (super.getTrace().isReturnPosition(i)) {
			final IReturnAction ret = (IReturnAction) super.getTrace().getSymbol(i);
			return ret.getAssignmentOfReturn();
		}
		final IInternalAction act = (IInternalAction) super.getTrace().getSymbol(i);
		if (mWithBranchEncoders) {
			if (act instanceof CodeBlock) {
				return ((CodeBlock) act).getTransitionFormulaWithBranchEncoders();
			}
			return act.getTransformula();
		}
		return act.getTransformula();
	}

	@Override
	protected UnmodifiableTransFormula getLocalVarAssignmentFromValidPos(final int i) {
		final ICallAction cb = (ICallAction) super.getTrace().getSymbol(i);
		return cb.getLocalVarsAssignment();
	}

	@Override
	protected UnmodifiableTransFormula getGlobalVarAssignmentFromValidPos(final int i) {
		final String calledProcedure = getCalledProcedure(i);
		return mModifiableGlobalVariableManager.getGlobalVarsAssignment(calledProcedure);

	}

	@Override
	protected UnmodifiableTransFormula getOldVarAssignmentFromValidPos(final int i) {
		final String calledProcedure = getCalledProcedure(i);
		return mModifiableGlobalVariableManager.getOldVarsAssignment(calledProcedure);
	}

	/**
	 * TODO: return set of all pending calls in case of InterproceduralSequentialComposition
	 */
	private String getCalledProcedure(final int i) {
		if (super.getTrace().isCallPosition(i)) {
			final ICallAction call = (ICallAction) super.getTrace().getSymbol(i);
			return call.getSucceedingProcedure();
		} else if (super.getTrace().isPendingReturn(i)) {
			final IReturnAction ret = (IReturnAction) super.getTrace().getSymbol(i);
			return ret.getPrecedingProcedure();
		} else {
			throw new UnsupportedOperationException("only available for call and pending return");
		}
	}

}
