/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPStateBottom<ACTION extends IIcfgTransition<IcfgLocation>> extends VPState<ACTION> {
	
	VPStateBottom(final VPDomain<ACTION> domain, final Set<IProgramVarOrConst> vars) {
		super(domain, vars);
	}
	
	@Override
	public boolean isBottom() {
		return true;
	}
	
	@Override
	public String toLogString() {
		return "VPStateBottom, Vars: " + getVariables();
	}
	
	@Override
	public boolean isTop() {
		return false;
	}
	
	@Override
	public VPState<ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mVars);
		newVariables.removeAll(variables);
		return mFactory.getBottomState(newVariables);
	}

	@Override
	public VPState<ACTION> removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}
	
	
	@Override
	public VPState<ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mVars);
		newVariables.addAll(variables);
		return mFactory.getBottomState(newVariables);
	}

	@Override
	public VPState<ACTION> addVariable(final IProgramVarOrConst variable) {
		return addVariables(Collections.singleton(variable));
	}
}
