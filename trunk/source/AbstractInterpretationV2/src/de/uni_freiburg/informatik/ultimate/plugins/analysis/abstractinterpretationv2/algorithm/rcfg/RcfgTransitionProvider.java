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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgTransitionProvider implements ITransitionProvider<CodeBlock, BoogieIcfgLocation> {

	@Override
	public Collection<CodeBlock> getSuccessors(final CodeBlock elem, final CodeBlock scope) {
		final IcfgLocation target = elem.getTarget();
		if (target == null) {
			return Collections.emptyList();
		}
		return RcfgUtils.getValidCodeBlocks(target.getOutgoingEdges(), scope);
	}

	@Override
	public boolean isSuccessorErrorLocation(final CodeBlock elem, final CodeBlock currentScope) {
		assert elem != null;

		if (elem instanceof Return) {
			if (!RcfgUtils.isAllowedReturn(elem, currentScope)) {
				return false;
			}
		}

		final IcfgLocation target = elem.getTarget();
		if (target instanceof BoogieIcfgLocation) {
			final BoogieIcfgLocation progPoint = (BoogieIcfgLocation) target;
			return progPoint.isErrorLocation();
		}
		return false;
	}

	@Override
	public String toLogString(final CodeBlock elem) {
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
	public boolean isLeavingScope(final CodeBlock current, final CodeBlock scope) {
		assert current != null;
		return RcfgUtils.isAllowedReturn(current, scope);
	}

	@Override
	public BoogieIcfgLocation getSource(final CodeBlock current) {
		return (BoogieIcfgLocation) current.getSource();
	}

	@Override
	public BoogieIcfgLocation getTarget(final CodeBlock current) {
		return (BoogieIcfgLocation) current.getTarget();
	}

	@Override
	public Collection<CodeBlock> getSuccessorActions(final BoogieIcfgLocation loc) {
		return loc.getOutgoingEdges().stream().map(e -> (CodeBlock) e).collect(Collectors.toList());
	}

	@Override
	public boolean isSummaryForCall(final CodeBlock action, final CodeBlock possibleCall) {
		return RcfgUtils.isSummaryForCall(action, possibleCall);
	}

	@Override
	public boolean isSummaryWithImplementation(final CodeBlock action) {
		return RcfgUtils.isSummaryWithImplementation(action);
	}

	@Override
	public String getProcedureName(final CodeBlock current) {
		if (current == null) {
			return null;
		}
		if (current instanceof Summary) {
			final Summary summary = (Summary) current;
			return summary.getCallStatement().getMethodName();
		}
		return current.getSucceedingProcedure();
	}

	@Override
	public CodeBlock getSummaryForCall(final CodeBlock call) {
		if (!(call instanceof Call)) {
			throw new IllegalArgumentException("call is not a Call");
		}
		return call.getSource().getOutgoingEdges().stream().map(a -> (CodeBlock) a)
				.filter(a -> isSummaryForCall(a, call)).findFirst().orElse(null);
	}
}
