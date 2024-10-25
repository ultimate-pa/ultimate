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

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class CfgThreadLocalState {
	private final IIcfgSymbolTable mSymbolTable;
	private final ThreadInstance mThread;
	private final BoogieIcfgLocation mLocation;
	private final Map<ILocalProgramVar, Object> mLocalState;

	public CfgThreadLocalState(final IIcfgSymbolTable symbolTable, final ThreadInstance thread,
			final BoogieIcfgLocation location, final Map<ILocalProgramVar, Object> localState) {
		mSymbolTable = Objects.requireNonNull(symbolTable);
		mThread = Objects.requireNonNull(thread);
		mLocation = Objects.requireNonNull(location);
		mLocalState = Objects.requireNonNull(localState);
	}

	public CfgThreadLocalState(final IIcfgSymbolTable symbolTable, final ThreadInstance thread) {
		mSymbolTable = Objects.requireNonNull(symbolTable);
		mThread = Objects.requireNonNull(thread);
		mLocation = null;
		mLocalState = null;
	}

	public ThreadInstance getThread() {
		return mThread;
	}

	public boolean isIdle() {
		return mLocation == null;
	}

	public BoogieIcfgLocation getLocation() {
		return mLocation;
	}

	public Object getLocal(final ILocalProgramVar localVar) {
		assert !isIdle() : "no variable values stored in idle state";
		final var value = mLocalState.get(localVar);
		assert value != null : "no value stored for local variable " + localVar + " of " + mThread;
		return value;
	}

	public CfgThreadLocalState updateLocation(final BoogieIcfgLocation newLocation) {
		return new CfgThreadLocalState(mSymbolTable, mThread, newLocation, mLocalState);
	}

	public CfgThreadLocalState updateLocal(final ILocalProgramVar localVar, final Object newValue) {
		assert mSymbolTable.getLocals(mThread.getTemplateName()).contains(localVar) : "unknown variable " + localVar
				+ " for thread " + mThread;

		final var newLocalState = new HashMap<>(mLocalState);
		newLocalState.put(localVar, newValue);
		return new CfgThreadLocalState(mSymbolTable, mThread, mLocation, newLocalState);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mLocalState, mLocation, mSymbolTable, mThread);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final CfgThreadLocalState other = (CfgThreadLocalState) obj;
		return Objects.equals(mLocalState, other.mLocalState) && Objects.equals(mLocation, other.mLocation)
				&& Objects.equals(mSymbolTable, other.mSymbolTable) && Objects.equals(mThread, other.mThread);
	}

	@Override
	public String toString() {
		return mThread + "[" + mLocation + "]:: " + mLocalState;
	}
}