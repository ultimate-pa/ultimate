/*
 * Copyright (C) 2025 Christof Schuster (christof.schuster@gmx.de)
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

/**
 * Wrapper class of a IcfgEdge for a Data Flow Graph Node for easier Implementation.
 *
 * @author christof.schuster@gmx.de
 */
public class DfgNode {
	private final IcfgEdge mEdge;

	public DfgNode(final IcfgEdge edge) {
		mEdge = edge;
	}

	public IcfgEdge getCorrespondingDFGEdge() {
		return mEdge;
	}

	@Override
	public String toString() {
		return mEdge.toString();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mEdge);
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
		final DfgNode other = (DfgNode) obj;
		return Objects.equals(mEdge, other.mEdge);
	}

}
