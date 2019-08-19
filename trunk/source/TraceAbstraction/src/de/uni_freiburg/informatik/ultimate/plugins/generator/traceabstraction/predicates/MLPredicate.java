/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Arrays;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents Predicate with multiple locations.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class MLPredicate extends BasicPredicate implements IMLPredicate {
	private static final long serialVersionUID = 1750137515726690834L;

	@Visualizable
	protected final IcfgLocation[] mProgramPoints;

	protected MLPredicate(final IcfgLocation[] programPoints, final int serialNumber, final String[] procedures,
			final Term term, final Set<IProgramVar> vars, final Term closedFormula) {
		super(serialNumber, procedures, term, vars, closedFormula);
		mProgramPoints = programPoints;
	}

	@Override
	public IcfgLocation[] getProgramPoints() {
		return mProgramPoints;
	}

	/**
	 * @return the mAssertion
	 */
	@Override
	public Term getFormula() {
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		return mClosedFormula;
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mVars;
	}

	@Override
	public String toString() {
		String result = super.mSerialNumber + "#";
		if (mProgramPoints != null) {
			result += Arrays.toString(mProgramPoints);
		}
		result += mFormula.toString();
		return result;
	}

	@Override
	public boolean isUnknown() {
		return false;
	}

}
