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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class IcfgTransitionProvider implements ITransitionProvider<IcfgEdge, IcfgLocation> {

	private final IIcfg<?> mIcfg;

	public IcfgTransitionProvider(final IIcfg<?> icfg) {
		mIcfg = icfg;
	}

	@Override
	public Collection<IcfgEdge> getSuccessors(final IcfgEdge elem, final IcfgEdge scope) {
		final IcfgLocation target = elem.getTarget();
		if (target == null) {
			return Collections.emptyList();
		}
		return target.getOutgoingEdges().stream().filter(a -> !(a instanceof IReturnAction) || isLeavingScope(a, scope))
				.collect(Collectors.toSet());
	}

	@Override
	public Collection<IcfgEdge> getPredecessors(final IcfgEdge elem, final IcfgEdge scope) {
		final IcfgLocation source = elem.getSource();
		if (source == null) {
			return Collections.emptyList();
		}
		return source.getIncomingEdges().stream().filter(a -> !(a instanceof ICallAction) || isEnteringScope(a, scope))
				.collect(Collectors.toSet());
	}

	@Override
	public String toLogString(final IcfgEdge elem) {
		return elem.toString();
	}

	@Override
	public boolean isEnteringScope(final IcfgEdge current) {
		return current instanceof IIcfgCallTransition<?>;
	}

	@Override
	public boolean isLeavingScope(final IcfgEdge current, final IcfgEdge scope) {
		assert current != null;
		if (current instanceof IIcfgReturnTransition<?, ?>) {
			return RcfgUtils.isAllowedReturn((IIcfgReturnTransition<?, ?>) current, scope);
		}
		return false;
	}

	@Override
	public boolean isEnteringScope(final IcfgEdge action, final IcfgEdge scope) {
		if (action instanceof IIcfgCallTransition<?> && scope instanceof IIcfgReturnTransition<?, ?>) {
			final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) action;
			final IIcfgReturnTransition<?, ?> retTran = (IIcfgReturnTransition<?, ?>) scope;
			return retTran.getCorrespondingCall().equals(call);
		}
		return false;
	}

	@Override
	public boolean isLeavingScope(final IcfgEdge action) {
		return action instanceof IIcfgReturnTransition<?, ?>;
	}

	@Override
	public IcfgLocation getSource(final IcfgEdge current) {
		return current.getSource();
	}

	@Override
	public IcfgLocation getTarget(final IcfgEdge current) {
		return current.getTarget();
	}

	@Override
	public Collection<IcfgEdge> getSuccessorActions(final IcfgLocation loc) {
		return loc.getOutgoingEdges().stream().collect(Collectors.toList());
	}

	@Override
	public Collection<IcfgEdge> getPredecessorActions(final IcfgLocation loc) {
		return loc.getIncomingEdges().stream().collect(Collectors.toList());
	}

	@Override
	public boolean isSummaryForCall(final IcfgEdge action, final IcfgEdge possibleCall) {
		if (action instanceof CodeBlock && possibleCall instanceof CodeBlock) {
			return RcfgUtils.isSummaryForCall(action, possibleCall);
		}
		return false;
	}

	@Override
	public boolean isSummaryWithImplementation(final IcfgEdge action) {
		return RcfgUtils.isSummaryWithImplementation(action);
	}

	@Override
	public String getProcedureName(final IcfgEdge current) {
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
	public IcfgEdge getSummaryForCall(final IcfgEdge call) {
		if (!(call instanceof ICallAction)) {
			throw new IllegalArgumentException("call is not a Call");
		}
		return call.getSource().getOutgoingEdges().stream().filter(a -> isSummaryForCall(a, call)).findFirst()
				.orElse(null);
	}

	@Override
	public boolean isErrorLocation(final IcfgLocation loc) {

		final String proc = loc.getProcedure();
		final Set<?> errors = mIcfg.getProcedureErrorNodes().get(proc);
		if (errors == null) {
			return false;
		}
		return errors.contains(loc);
	}

}
