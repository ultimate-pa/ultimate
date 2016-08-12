/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DataflowState implements IAbstractState<DataflowState, CodeBlock, IProgramVar> {

	@Override
	public DataflowState addVariable(final IProgramVar variable) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public DataflowState removeVariable(final IProgramVar variable) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public DataflowState addVariables(final Collection<IProgramVar> variables) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public DataflowState removeVariables(final Collection<IProgramVar> variables) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean containsVariable(final IProgramVar var) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<IProgramVar> getVariables() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public DataflowState patch(final DataflowState dominator) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isBottom() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isEqualTo(final DataflowState other) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState.SubsetResult
			isSubsetOf(final DataflowState other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term getTerm(final Script script, final Boogie2SMT bpl2smt) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toLogString() {
		// TODO Auto-generated method stub
		return null;
	}

}
