/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;

/**
 * Default implementation of {@link IProgramFunction}.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class ProgramFunction implements IProgramFunction {
	private static final long serialVersionUID = 1302187663322649145L;

	private final FunctionSymbol mFunSym;

	public ProgramFunction(final FunctionSymbol funSym) {
		super();
		Objects.nonNull(funSym);
		mFunSym = funSym;
	}

	@Override
	public FunctionSymbol getFunctionSymbol() {
		return mFunSym;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mFunSym == null) ? 0 : mFunSym.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final ProgramFunction other = (ProgramFunction) obj;
		if (mFunSym == null) {
			if (other.mFunSym != null)
				return false;
		} else if (!mFunSym.equals(other.mFunSym))
			return false;
		return true;
	}

}
