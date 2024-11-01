/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule.RuleInstance;

public class CfgRuleIndependence<S> implements IIndependenceRelation<S, RuleInstance<S>> {
	private final IIndependenceRelation<?, ? super IcfgEdge> mUnderlying;

	public CfgRuleIndependence(final IIndependenceRelation<?, ? super IcfgEdge> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public Dependence isIndependent(final S state, final RuleInstance<S> a, final RuleInstance<S> b) {
		final var aRule = (CfgRule<?>) a.getRule();
		final var bRule = (CfgRule<?>) b.getRule();

		// If the rule instances involve the same thread, we consider them dependent.
		assert a.getThreads().length == 1;
		assert b.getThreads().length == 1;
		if (a.getThreads()[0] == b.getThreads()[0]) {
			return Dependence.DEPENDENT;
		}

		return mUnderlying.isIndependent(null, aRule.mEdge, bRule.mEdge);
	}
}
