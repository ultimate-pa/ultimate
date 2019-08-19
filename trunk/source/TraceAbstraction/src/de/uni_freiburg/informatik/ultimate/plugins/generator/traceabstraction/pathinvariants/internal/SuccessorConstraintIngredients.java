/*
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

import java.util.Set;

/**
 * The ingredients necessary to construct invariant constraints.
 *
 * @param <IPT>
 *            Invariant Pattern Type
 */
public class SuccessorConstraintIngredients<IPT> {
	private final IcfgLocation mSourceLocation;
	private final Set<IProgramVar> mVariablesForSourcePattern;
	private final IPT mInvStart;

	private final Map<IcfgEdge, IPT> mEdge2Pattern;
	private final Map<IcfgEdge, IPT> mEdge2TargetInv;
	private final Map<IcfgEdge, Set<IProgramVar>> mEdge2VariablesForTargetPattern;

	public SuccessorConstraintIngredients(final IcfgLocation sourceLocation,
			final Set<IProgramVar> variablesForSourcePattern, final IPT invStart) {
		super();
		mSourceLocation = sourceLocation;
		mVariablesForSourcePattern = variablesForSourcePattern;
		mInvStart = invStart;
		mEdge2Pattern = new HashMap<>();
		mEdge2TargetInv = new HashMap<>();
		mEdge2VariablesForTargetPattern = new HashMap<>();
	}

	public void addTransition(final IcfgEdge icfgEdge, final IPT ipt, final Set<IProgramVar> varsTargetPattern) {
		if (!icfgEdge.getSource().equals(mSourceLocation)) {
			throw new IllegalArgumentException("incompatible source location " + icfgEdge.getSource());
		}
		final IPT oldIpt = mEdge2TargetInv.put(icfgEdge, ipt);
		if (oldIpt != null) {
			throw new IllegalArgumentException("edge already added " + icfgEdge);
		}
		final Set<IProgramVar> oldVars = mEdge2VariablesForTargetPattern.put(icfgEdge, varsTargetPattern);
		if (oldVars != null) {
			throw new IllegalArgumentException("vars already added " + icfgEdge);
		}
	}

	public void addTransition(final IcfgEdge icfgEdge, final IPT ipt, final Set<IProgramVar> varsTargetPattern,
			final IPT transitionPattern) {
		addTransition(icfgEdge, ipt, varsTargetPattern);
		mEdge2Pattern.put(icfgEdge, transitionPattern);
	}

	public Set<TransitionConstraintIngredients<IPT>> buildTransitionConstraintIngredients() {
		final Set<TransitionConstraintIngredients<IPT>> result = new HashSet<>();
		for (final Entry<IcfgEdge, IPT> entry : mEdge2TargetInv.entrySet()) {
			result.add(new TransitionConstraintIngredients<IPT>(mInvStart, entry.getValue(), mSourceLocation,
					entry.getKey().getTarget(), mVariablesForSourcePattern,
					mEdge2VariablesForTargetPattern.get(entry.getKey()), entry.getKey().getTransformula()));

		}
		return result;
	}

	public IcfgLocation getSourceLocation() {
		return mSourceLocation;
	}

	public Set<IProgramVar> getVariablesForSourcePattern() {
		return mVariablesForSourcePattern;
	}

	public IPT getInvStart() {
		return mInvStart;
	}

	public Map<IcfgEdge, IPT> getEdge2Pattern() {
		return mEdge2Pattern;
	}

	public Map<IcfgEdge, IPT> getEdge2TargetInv() {
		return mEdge2TargetInv;
	}

	public Map<IcfgEdge, Set<IProgramVar>> getEdge2VariablesForTargetPattern() {
		return mEdge2VariablesForTargetPattern;
	}
}
