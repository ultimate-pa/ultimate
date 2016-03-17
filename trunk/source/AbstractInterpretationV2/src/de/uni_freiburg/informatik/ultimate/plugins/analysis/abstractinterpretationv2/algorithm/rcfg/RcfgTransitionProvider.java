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

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgTransitionProvider implements ITransitionProvider<CodeBlock, ProgramPoint> {

	@Override
	public Collection<CodeBlock> getSuccessors(CodeBlock elem, CodeBlock scope) {
		final RCFGNode target = elem.getTarget();
		if (target == null) {
			return Collections.emptyList();
		}
		return RcfgUtils.getValidCodeBlocks(target.getOutgoingEdges(), scope);
	}

	@Override
	public boolean isPostErrorLocation(CodeBlock elem, CodeBlock currentScope) {
		assert elem != null;

		if (elem instanceof Return) {
			if (!RcfgUtils.isAllowedReturn(elem, currentScope)) {
				return false;
			}
		}

		final RCFGNode target = elem.getTarget();
		if (target instanceof ProgramPoint) {
			final ProgramPoint progPoint = (ProgramPoint) target;
			return progPoint.isErrorLocation();
		}
		return false;
	}

	@Override
	public String toLogString(CodeBlock elem) {
		return elem.toString();
	}

	@Override
	public Collection<CodeBlock> filterInitialElements(final Collection<CodeBlock> elems) {
		if (elems == null) {
			return Collections.emptyList();
		}
		return elems.stream().filter(e -> !RcfgUtils.isSummaryWithImplementation(e)).collect(Collectors.toList());
	}

	@Override
	public boolean isEnteringScope(final CodeBlock current) {
		return current instanceof Call;
	}

	@Override
	public boolean isLeavingScope(CodeBlock current, CodeBlock scope) {
		assert current != null;
		return RcfgUtils.isAllowedReturn(current, scope);
	}

	@Override
	public ProgramPoint getSource(final CodeBlock current) {
		return (ProgramPoint) current.getSource();
	}

	@Override
	public ProgramPoint getTarget(final CodeBlock current) {
		return (ProgramPoint) current.getTarget();
	}

	@Override
	public Collection<CodeBlock> getSuccessorActions(ProgramPoint loc) {
		return loc.getOutgoingEdges().stream().map(e -> (CodeBlock) e).collect(Collectors.toList());
	}

	@Override
	public boolean isSummaryForCall(CodeBlock action, CodeBlock possibleCall) {
		return RcfgUtils.isSummaryForCall(action, possibleCall);
	}

	@Override
	public boolean isSummaryWithImplementation(CodeBlock action) {
		return RcfgUtils.isSummaryWithImplementation(action);
	}
}
