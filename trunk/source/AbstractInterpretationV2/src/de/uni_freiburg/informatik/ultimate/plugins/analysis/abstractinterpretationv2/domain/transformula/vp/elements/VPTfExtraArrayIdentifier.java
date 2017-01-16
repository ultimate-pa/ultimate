/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPTfExtraArrayIdentifier extends VPTfArrayIdentifier {

	public VPTfExtraArrayIdentifier(IProgramVarOrConst pvoc, ArrayInOutStatus inOutStatus) {
		super(pvoc, inOutStatus);
	}

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		if (getProgramVarOrConst() instanceof IProgramVar 
				&& isInOrThrough()) {
			return Collections.singletonMap((IProgramVar) getProgramVarOrConst(), null);
		} else {
			return Collections.emptyMap();
		}
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		if (getProgramVarOrConst() instanceof IProgramVar 
				&& isInOrThrough()) {
			return Collections.singletonMap((IProgramVar) getProgramVarOrConst(), null);
		} else {
			return Collections.emptyMap();
		}
	}

	
}
