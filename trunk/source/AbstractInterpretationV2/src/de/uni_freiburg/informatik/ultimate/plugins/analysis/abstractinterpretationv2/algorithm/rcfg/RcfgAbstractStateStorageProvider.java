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

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, LOCATION, VARDECL>
		extends BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> {

	private final Map<LOCATION, AbstractMultiState<STATE, CodeBlock, VARDECL>> mStorage;

	public RcfgAbstractStateStorageProvider(final IAbstractStateBinaryOperator<STATE> mergeOperator,
			final IUltimateServiceProvider services, final ITransitionProvider<CodeBlock, LOCATION> transprovider) {
		this(mergeOperator, services, transprovider, null);
	}

	public RcfgAbstractStateStorageProvider(final IAbstractStateBinaryOperator<STATE> mergeOperator,
			final IUltimateServiceProvider services, final ITransitionProvider<CodeBlock, LOCATION> transprovider,
			final CodeBlock scope) {
		super(mergeOperator, services, transprovider, scope);
		mStorage = new HashMap<>();
	}

	@Override
	protected AbstractMultiState<STATE, CodeBlock, VARDECL> getPostState(final CodeBlock action) {
		assert action != null;
		final LOCATION node = getTransitionProvider().getTarget(action);
		return mStorage.get(node);
	}

	@Override
	protected void replacePostState(final CodeBlock action,
			final AbstractMultiState<STATE, CodeBlock, VARDECL> newState) {
		assert action != null;
		final LOCATION node = getTransitionProvider().getTarget(action);
		mStorage.put(node, newState);
	}

	@Override
	public BaseRcfgAbstractStateStorageProvider<STATE, LOCATION, VARDECL> create(final CodeBlock scope) {
		return new RcfgAbstractStateStorageProvider<>(getMergeOperator(), getServices(), getTransitionProvider(),
				scope);
	}

	@Override
	public String toString() {
		if (mStorage == null) {
			return "NULL";
		}
		if (mStorage.isEmpty()) {
			return "{}";
		}
		final StringBuilder sb = new StringBuilder().append('{');
		final Set<Entry<LOCATION, AbstractMultiState<STATE, CodeBlock, VARDECL>>> entries = mStorage.entrySet();
		for (final Entry<LOCATION, AbstractMultiState<STATE, CodeBlock, VARDECL>> entry : entries) {
			sb.append(entry.getKey().toString()).append("=[");
			final AbstractMultiState<STATE, CodeBlock, VARDECL> state = entry.getValue();
			if (!state.isEmpty()) {
				sb.append(state.toLogString());
			}
			sb.append("], ");
		}
		if (!entries.isEmpty()) {
			sb.delete(sb.length() - 2, sb.length());
		}
		sb.append('}');
		return sb.toString();
	}
}
