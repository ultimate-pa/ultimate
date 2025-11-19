/*
 * Copyright (C) 2025 University of Freiburg
 * Copyright (C) 2025 LMU Munich
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

class ProgramVariableTransferrer {
	private final ConstructionCache<ILocalProgramVar, ILocalProgramVar> mILocalProgramVarCC;
	private final ConstructionCache<IProgramNonOldVar, IProgramNonOldVar> mIProgramNonOldVarCC;
	private final ConstructionCache<IProgramConst, IProgramConst> mIProgramConstCC;

	public ProgramVariableTransferrer(final TermTransferrer transferrer, final ManagedScript targetScript) {
		mILocalProgramVarCC = new ConstructionCache<>(new IValueConstruction<ILocalProgramVar, ILocalProgramVar>() {

			@Override
			public ILocalProgramVar constructValue(final ILocalProgramVar oldPv) {
				targetScript.lock(this);
				final ILocalProgramVar newPv =
						(ILocalProgramVar) ProgramVarUtils.transferProgramVar(transferrer, oldPv);
				targetScript.unlock(this);
				return newPv;
			}
		});
		mIProgramNonOldVarCC = new ConstructionCache<>(new IValueConstruction<IProgramNonOldVar, IProgramNonOldVar>() {

			@Override
			public IProgramNonOldVar constructValue(final IProgramNonOldVar oldPv) {
				targetScript.lock(this);
				final IProgramNonOldVar newPv =
						(IProgramNonOldVar) ProgramVarUtils.transferProgramVar(transferrer, oldPv);
				targetScript.unlock(this);
				return newPv;
			}

		});
		mIProgramConstCC = new ConstructionCache<>(oldPv -> {
			final String newIdentifier = oldPv.getIdentifier();
			final ApplicationTerm newSmtConstant = (ApplicationTerm) transferrer.transform(oldPv.getDefaultConstant());
			return new ProgramConst(newIdentifier, newSmtConstant, false);
		});
	}

	public ILocalProgramVar getOrConstruct(final ILocalProgramVar key) {
		return mILocalProgramVarCC.getOrConstruct(key);
	}

	public IProgramNonOldVar getOrConstruct(final IProgramNonOldVar key) {
		return mIProgramNonOldVarCC.getOrConstruct(key);
	}

	public IProgramOldVar getOrConstruct(final IProgramOldVar key) {
		return mIProgramNonOldVarCC.getOrConstruct(key.getNonOldVar()).getOldVar();
	}

	public IProgramConst getOrConstruct(final IProgramConst key) {
		return mIProgramConstCC.getOrConstruct(key);
	}

	public Map<ILocalProgramVar, ILocalProgramVar> getILocalProgramVarMap() {
		return Collections.unmodifiableMap(mILocalProgramVarCC);
	}

	public Map<IProgramNonOldVar, IProgramNonOldVar> getIProgramNonOldVarMap() {
		return Collections.unmodifiableMap(mIProgramNonOldVarCC);
	}

	public Map<IProgramConst, IProgramConst> getIProgramConstMap() {
		return Collections.unmodifiableMap(mIProgramConstCC);
	}

	public Map<Term, Term> getIProgramConstTermMap() {
		return getIProgramConstMap().entrySet().stream().collect(
				Collectors.toMap(x -> x.getKey().getDefaultConstant(), x -> x.getValue().getDefaultConstant()));
	}

	public IProgramVar translateProgramVar(final IProgramVar pv) {
		IProgramVar result;
		if (pv instanceof ILocalProgramVar) {
			result = getILocalProgramVarMap().get(pv);
		} else if (pv instanceof IProgramNonOldVar) {
			result = getIProgramNonOldVarMap().get(pv);
		} else if (pv instanceof IProgramOldVar) {
			result = getIProgramNonOldVarMap().get(((IProgramOldVar) pv).getNonOldVar()).getOldVar();
		} else {
			throw new UnsupportedOperationException(pv.getClass().getSimpleName());
		}
		assert result != null;
		return result;
	}

	public IProgramConst translateProgramConst(final IProgramConst pc) {
		return getIProgramConstMap().get(pc);
	}

}