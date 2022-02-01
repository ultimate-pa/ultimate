/*
 * Copyright (C) 2015-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 *
 * An {@link IVariableProvider} creates abstract states that track certain variables according to the actions that
 * should happen before or after.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of states that are created by this {@link IVariableProvider}. Must be a subtype of
 *            {@link IAbstractState}.
 * @param <ACTION>
 *            The type of action that should be considered by this {@link IVariableProvider}.
 * @param <VARDECL>
 *            The type of variables defined by the abstract state interface.
 */
public interface IVariableProvider<STATE extends IAbstractState<STATE>, ACTION> {

	/**
	 * Defines global and local variables in an {@link IAbstractState} before the execution of action
	 * <code>current</code>. Will be called for initial edges of a program and for a fresh state.<br>
	 *
	 * Note that
	 * <ul>
	 * <li>Assume that <code>state</code> is fresh (i.e., <code>{@link IAbstractState#isEmpty()} == true</code>).
	 * </ul>
	 *
	 * @param current
	 *            The action that will be executed on <code>state</code>.
	 * @param state
	 *            A fresh {@link IAbstractState}.
	 * @return An {@link IAbstractState} that contains all global and local variables according to the position of
	 *         <code>current</code> in the program.
	 */
	STATE defineInitialVariables(ACTION current, STATE state);

	/**
	 * Should prepare an {@link IAbstractState} with insertion or removal of variables s.t.
	 * <ul>
	 * <li>All variables that are still in scope are untouched.
	 * <li>Fresh variables in the scope are added.
	 * <li>Variables that are masked by a new scope (i.e., variables with the same name) are removed and replaced by
	 * fresh variables.
	 * <li>Variables that are local to an old scope have to be restored.
	 * <li>Variables that are unmasked by an old scope have to be restored.
	 * </ul>
	 *
	 * @param current
	 *            The action that will be executed on <code>state</code>.
	 * @param localPreState
	 *            The current {@link IAbstractState}.
	 * @param hierachicalPreState
	 *            The {@link IAbstractState} that was the prestate before entering the current scope.
	 * @return An {@link IAbstractState} that contains all variables that are necessary to represent the effects of
	 *         <code>current</code> and that are visible in the scope after execution of <code>current</code>.
	 */
	STATE defineVariablesAfter(final ACTION current, final STATE localPreState, final STATE hierachicalPreState);

	STATE createValidPostOpStateAfterLeaving(ACTION act, STATE origPreLinState, STATE preHierState);

	STATE createValidPostOpStateBeforeLeaving(final ACTION action, final STATE stateHier);

	IVariableProvider<STATE, ACTION> createNewVariableProvider(CfgSmtToolkit toolkit);

	Set<IProgramVarOrConst> getRequiredVars(ACTION act);

}
