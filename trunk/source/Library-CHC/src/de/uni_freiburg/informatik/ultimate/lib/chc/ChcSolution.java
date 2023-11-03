/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class ChcSolution extends BasePayloadContainer {
	private static final long serialVersionUID = -4389502364282768199L;

	private final LBool mSatisfiability;
	private final Model mModel;
	private final Derivation mDerivation;
	private final Set<HornClause> mUnsatCore;

	private ChcSolution(final LBool satisfiability, final Model model, final Derivation derivation,
			final Set<HornClause> unsatCore) {
		mSatisfiability = satisfiability;
		mModel = model;
		mDerivation = derivation;
		mUnsatCore = unsatCore;
	}

	public static ChcSolution sat(final Model model) {
		return new ChcSolution(LBool.SAT, model, null, null);
	}

	public static ChcSolution unsat(final Derivation derivation, final Set<HornClause> unsatCore) {
		return new ChcSolution(LBool.UNSAT, null, derivation, unsatCore);
	}

	public static ChcSolution unknown() {
		return new ChcSolution(LBool.UNKNOWN, null, null, null);
	}

	public LBool getSatisfiability() {
		return mSatisfiability;
	}

	public Model getModel() {
		return mModel;
	}

	public Derivation getDerivation() {
		return mDerivation;
	}

	public Set<HornClause> getUnsatCore() {
		return mUnsatCore;
	}
}
