/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgTransitionProvider implements ITransitionProvider<CodeBlock> {

	@Override
	public Collection<CodeBlock> getSuccessors(CodeBlock elem, CodeBlock scope) {
		final RCFGNode target = elem.getTarget();
		if (target == null) {
			return Collections.emptyList();
		}
		final List<RCFGEdge> successors = target.getOutgoingEdges();
		final Collection<CodeBlock> rtr = getValidCodeBlocks(successors, scope);
		return rtr;
	}

	@Override
	public boolean isPostErrorLocation(CodeBlock elem, CodeBlock currentScope) {
		assert elem != null;

		if (elem instanceof Return) {
			if (!isCorrespondingCall(elem, currentScope)) {
				return false;
			}
		}

		final RCFGNode target = elem.getTarget();
		if (target instanceof ProgramPoint) {
			ProgramPoint progPoint = (ProgramPoint) target;
			return progPoint.isErrorLocation();
		}
		return false;
	}

	@Override
	public String toLogString(CodeBlock elem) {
		return elem.toString();
	}

	@Override
	public Collection<CodeBlock> filterInitialElements(Collection<CodeBlock> elems) {
		if (elems == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(elems.size());
		for (final CodeBlock elem : elems) {
			if (!isUnnecessarySummary(elem)) {
				rtr.add(elem);
			}
		}
		return rtr;
	}

	@Override
	public boolean isEnteringScope(CodeBlock current) {
		if (current instanceof Call) {
			return true;
		}
		return false;
	}

	@Override
	public boolean isLeavingScope(CodeBlock current, CodeBlock scope) {
		assert current != null;
		return isCorrespondingCall(current, scope);
	}

	private Collection<CodeBlock> getValidCodeBlocks(final Collection<RCFGEdge> successors, CodeBlock scope) {
		if (successors == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(successors.size());
		for (final RCFGEdge successor : successors) {
			final CodeBlock cbSucc = getValidCodeBlock(successor, scope);
			if (cbSucc == null) {
				continue;
			}
			rtr.add(cbSucc);
		}
		return rtr;
	}

	private CodeBlock getValidCodeBlock(final RCFGEdge successor, CodeBlock scope) {
		if (!(successor instanceof CodeBlock)) {
			return null;
		}
		if (isUnnecessarySummary(successor)) {
			return null;
		}

		final CodeBlock cbSucc = (CodeBlock) successor;
		if (cbSucc instanceof Return) {
			if (!isCorrespondingCall(cbSucc, scope)) {
				return null;
			}
		}
		return (CodeBlock) successor;
	}

	private boolean isUnnecessarySummary(RCFGEdge edge) {
		if (edge instanceof Summary) {
			Summary sum = (Summary) edge;
			return sum.calledProcedureHasImplementation();
		}
		return false;
	}

	private boolean isCorrespondingCall(CodeBlock current, CodeBlock currentScope) {
		if(currentScope == null){
			return false;
		}
		if (current instanceof Return) {
			Return currReturn = (Return) current;
			assert currentScope instanceof Call;
			return currReturn.getCorrespondingCall().equals(currentScope);
		}
		return false;
	}
}
