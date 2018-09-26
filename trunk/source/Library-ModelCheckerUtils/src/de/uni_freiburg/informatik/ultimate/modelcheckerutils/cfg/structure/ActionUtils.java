/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * {@link ActionUtils} provide utilities that target {@link IAction} instances.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ActionUtils {

	private ActionUtils() {
		// do not instantiate utility class
	}

	/**
	 * This method creates a fresh deep copy (i.e., including the {@link TransFormula}) of the provided {@link IAction}
	 * instance.
	 *
	 * @param script
	 *            {@link ManagedScript} that was used to construct the {@link Term}s of the original {@link IAction}
	 *            instance.
	 * @param action
	 *            input {@link IAction}.
	 * @return a copy if the input {@link IAction} .
	 *
	 * @see {@link TransFormulaBuilder#constructCopy(ManagedScript, de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula, java.util.Collection, java.util.Collection, java.util.Map)
	 */
	public static IAction constructCopy(final ManagedScript script, final IAction action) {
		if (action == null) {
			return null;
		}
		final IAction rtr;
		if (action instanceof IInternalAction) {
			final UnmodifiableTransFormula oldTf = action.getTransformula();
			final UnmodifiableTransFormula newTf = TransFormulaBuilder.constructCopy(script, oldTf,
					Collections.emptySet(), Collections.emptySet(), Collections.emptyMap());
			rtr = new BasicInternalAction(action.getPrecedingProcedure(), action.getSucceedingProcedure(), newTf);
		} else if (action instanceof ICallAction) {
			final UnmodifiableTransFormula oldTf = ((ICallAction) action).getLocalVarsAssignment();
			final UnmodifiableTransFormula newTf = TransFormulaBuilder.constructCopy(script, oldTf,
					Collections.emptySet(), Collections.emptySet(), Collections.emptyMap());
			rtr = new BasicCallAction(action.getPrecedingProcedure(), action.getSucceedingProcedure(), newTf);
		} else if (action instanceof IReturnAction) {
			final IReturnAction rAction = (IReturnAction) action;
			final UnmodifiableTransFormula oldAORTf = rAction.getAssignmentOfReturn();
			final UnmodifiableTransFormula oldLVACTf = rAction.getLocalVarsAssignmentOfCall();
			final UnmodifiableTransFormula newAORTf = TransFormulaBuilder.constructCopy(script, oldAORTf,
					Collections.emptySet(), Collections.emptySet(), Collections.emptyMap());
			final UnmodifiableTransFormula newLVACTf = TransFormulaBuilder.constructCopy(script, oldLVACTf,
					Collections.emptySet(), Collections.emptySet(), Collections.emptyMap());
			rtr = new BasicReturnAction(action.getPrecedingProcedure(), action.getSucceedingProcedure(), newAORTf,
					newLVACTf);
		} else if (action instanceof IForkActionThreadCurrent) {
			final IForkActionThreadCurrent fAction = (IForkActionThreadCurrent) action;
			fAction.getTransformula();
			rtr = new BasicForkActionCurrent(action.getPrecedingProcedure(), action.getSucceedingProcedure(),
					fAction.getTransformula(), fAction.getForkSmtArguments(), fAction.getNameOfForkedProcedure());
		} else if (action instanceof IJoinActionThreadCurrent) {
			final IJoinActionThreadCurrent fAction = (IJoinActionThreadCurrent) action;
			rtr = new BasicJoinActionCurrent(action.getPrecedingProcedure(), action.getSucceedingProcedure(),
					fAction.getTransformula(), fAction.getJoinSmtArguments());
		} else {
			throw new UnsupportedOperationException("(Yet) unknown IAction subtype: " + action.getClass());
		}

		return rtr;
	}
}
