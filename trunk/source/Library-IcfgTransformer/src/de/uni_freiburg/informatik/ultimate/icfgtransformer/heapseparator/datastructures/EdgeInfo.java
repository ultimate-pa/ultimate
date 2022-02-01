/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Wrapper for an IcfgEdge that carries information about the edge that we are interested in in the heap separator.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EdgeInfo {
	IcfgEdge mEdge;

	public EdgeInfo(final IcfgEdge edge) {
		mEdge = edge;
	}

	/**
	 * @param term
	 * @return
	 */
	public IProgramVarOrConst getProgramVarOrConstForTerm(final Term term) {
		return TransFormulaUtils.getProgramVarOrConstForTerm(mEdge.getTransformula(), term);
	}

	public IcfgLocation getSourceLocation() {
		return mEdge.getSource();
	}

	public IcfgEdge getEdge() {
		return mEdge;
	}

	@Override
	public String toString() {
		return "(" + mEdge + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mEdge == null) ? 0 : mEdge.hashCode());
		return result;
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
		final EdgeInfo other = (EdgeInfo) obj;
		if (mEdge == null) {
			if (other.mEdge != null) {
				return false;
			}
		} else if (!mEdge.equals(other.mEdge)) {
			return false;
		}
		return true;
	}

	public IProgramVar getInVar(final Term term) {
		if (!(term instanceof TermVariable)) {
			return null;
		}
		for (final Entry<IProgramVar, TermVariable> en : mEdge.getTransformula().getInVars().entrySet()) {
			if (en.getValue().equals(term)) {
				return en.getKey();
			}
		}
		return null;
	}

	public IProgramVar getOutVar(final Term term) {
		if (!(term instanceof TermVariable)) {
			return null;
		}
		for (final Entry<IProgramVar, TermVariable> en : mEdge.getTransformula().getOutVars().entrySet()) {
			if (en.getValue().equals(term)) {
				return en.getKey();
			}
		}
		return null;
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return mEdge.getTransformula().getInVars();
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mEdge.getTransformula().getOutVars();
	}

	public Set<TermVariable> getAuxVars() {
		return mEdge.getTransformula().getAuxVars();
	}

	public Set<IProgramConst> getNonTheoryConsts() {
		return mEdge.getTransformula().getNonTheoryConsts();
	}


}