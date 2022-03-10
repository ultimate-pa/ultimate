/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

public class VarAbsConstraints<L extends IAction> {
	private final Map<L, Set<IProgramVar>> mInConstr;
	private final Map<L, Set<IProgramVar>> mOutConstr;

	public VarAbsConstraints(final Map<L, Set<IProgramVar>> in, final Map<L, Set<IProgramVar>> out) {
		mInConstr = in;
		mOutConstr = out;
	}

	public Set<IProgramVar> getInConstraints(final L letter) {
		if (mInConstr.containsKey(letter)) {
			return Collections.unmodifiableSet(mInConstr.get(letter));
		}
		return Collections.emptySet();
	}

	public Set<IProgramVar> getOutConstraints(final L letter) {
		if (mOutConstr.containsKey(letter)) {
			return Collections.unmodifiableSet(mOutConstr.get(letter));
		}
		return Collections.emptySet();
	}

	public Map<L, Set<IProgramVar>> getInContraintsMap() {
		return mInConstr;
	}

	public Map<L, Set<IProgramVar>> getOutContraintsMap() {
		return mOutConstr;
	}


	@Override
	public int hashCode() {
		// TODO consider caching this
		return Objects.hash(mInConstr, mOutConstr);
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
		final VarAbsConstraints other = (VarAbsConstraints) obj;
		return Objects.equals(mInConstr, other.mInConstr) && Objects.equals(mOutConstr, other.mOutConstr);
	}
}
