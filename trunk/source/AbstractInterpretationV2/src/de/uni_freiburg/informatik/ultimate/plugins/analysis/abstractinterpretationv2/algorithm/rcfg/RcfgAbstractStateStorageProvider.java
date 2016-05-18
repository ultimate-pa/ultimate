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

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>, LOCATION>
		extends BaseRcfgAbstractStateStorageProvider<STATE, LOCATION> {

	private final Map<LOCATION, Deque<STATE>> mStorage;

	public RcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<STATE> mergeOperator,
			IUltimateServiceProvider services, ITransitionProvider<CodeBlock, LOCATION> transprovider) {
		super(mergeOperator, services, transprovider);
		mStorage = new HashMap<>();
	}

	protected Deque<STATE> getPostStates(CodeBlock action) {
		assert action != null;
		final LOCATION node = getTransitionProvider().getTarget(action);
		Deque<STATE> rtr = mStorage.get(node);
		if (rtr == null) {
			rtr = new ArrayDeque<STATE>();
			mStorage.put(node, rtr);
		}
		return rtr;
	}

	@Override
	public BaseRcfgAbstractStateStorageProvider<STATE, LOCATION> create() {
		return new RcfgAbstractStateStorageProvider<STATE, LOCATION>(getMergeOperator(), getServices(),
				getTransitionProvider());
	}

	@Override
	public String toString() {
		if (mStorage == null) {
			return "NULL";
		}
		if (mStorage.isEmpty()) {
			return "{}";
		}
		final StringBuilder sb = new StringBuilder('{');
		for (final Entry<?, Deque<STATE>> entry : mStorage.entrySet()) {
			sb.append(entry.getKey().toString()).append("=[");
			if (!entry.getValue().isEmpty()) {
				for (final STATE state : entry.getValue()) {
					sb.append(state.toLogString()).append(',');
				}
			}
			sb.append(']');
		}
		sb.append('}');
		return sb.toString();
	}
}
