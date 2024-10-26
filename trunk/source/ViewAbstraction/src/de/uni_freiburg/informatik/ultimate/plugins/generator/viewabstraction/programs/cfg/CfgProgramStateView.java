/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.interpreter.IValuation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;

public class CfgProgramStateView implements IValuation<CfgProgramStateView> {
	private final IIcfgSymbolTable mSymbolTable;
	private final Map<IProgramNonOldVar, Object> mGlobalState;
	private final CfgThreadLocalState mLocalState;

	public CfgProgramStateView(final IIcfgSymbolTable symbolTable, final Map<IProgramNonOldVar, Object> globalState,
			final CfgThreadLocalState localState) {
		mSymbolTable = symbolTable;
		mGlobalState = globalState;
		mLocalState = localState;
	}

	@Override
	public int getInteger(final String variable) {
		return (int) getVariable(variable);
	}

	@Override
	public boolean getBoolean(final String variable) {
		return (boolean) getVariable(variable);
	}

	private Object getVariable(final String variable) {
		final var global = getGlobal(variable);
		if (global != null) {
			return mGlobalState.get(global);
		}

		final var local = getLocal(variable);
		if (local != null) {
			return mLocalState.getLocal(local);
		}

		throw new IllegalArgumentException("unknown variable: " + variable);
	}

	@Override
	public CfgProgramStateView updateInteger(final String variable, final int newValue) {
		return updateVariable(variable, newValue);
	}

	@Override
	public CfgProgramStateView updateBoolean(final String variable, final boolean newValue) {
		return updateVariable(variable, newValue);
	}

	private CfgProgramStateView updateVariable(final String variable, final Object newValue) {
		final var global = getGlobal(variable);
		if (global != null) {
			final var newState = new HashMap<>(mGlobalState);
			newState.put(global, newValue);
			return new CfgProgramStateView(mSymbolTable, newState, mLocalState);
		}

		final var local = getLocal(variable);
		if (local != null) {
			final var newState = mLocalState.updateLocal(local, newValue);
			return new CfgProgramStateView(mSymbolTable, mGlobalState, newState);
		}

		throw new IllegalArgumentException("unknown variable: " + variable);
	}

	private IProgramNonOldVar getGlobal(final String variable) {
		return mSymbolTable.getGlobals().stream().filter(pv -> pv.getIdentifier().equals(variable)).findAny()
				.orElse(null);
	}

	private ILocalProgramVar getLocal(final String variable) {
		return mSymbolTable.getLocals(mLocalState.getTemplateName()).stream()
				.filter(pv -> pv.getIdentifier().equals(variable)).findAny().orElse(null);
	}

	public Map<IProgramNonOldVar, Object> getGlobalState() {
		return Collections.unmodifiableMap(mGlobalState);
	}

	public CfgThreadLocalState getLocalState() {
		return mLocalState;
	}
}