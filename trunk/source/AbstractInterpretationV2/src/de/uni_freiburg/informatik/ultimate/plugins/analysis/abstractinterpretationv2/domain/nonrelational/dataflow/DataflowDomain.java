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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Domain that can be used to compute fixpoints for various dataflow analyses like reaching definitions, def-use, etc.
 *
 * TODO: Implement on transformulas
 * <ul>
 * <li>reaching definitions
 * <li>live variable analysis (reaching definitions w/o overextend)
 * <li>"definitions", i.e., collection of writes
 * </ul>
 *
 *
 * Note: This domain is work in progress and does not work.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class DataflowDomain implements IAbstractDomain<DataflowState, CodeBlock, IProgramVar> {

	private final DataflowPostOperator mPost;
	private final DataflowMergeOperator mMerge;
	private final ILogger mLogger;

	public DataflowDomain(final ILogger logger) {
		mPost = new DataflowPostOperator();
		mMerge = new DataflowMergeOperator();
		mLogger = logger;
	}

	@Override
	public DataflowState createFreshState() {
		return new DataflowState();
	}

	@Override
	public IAbstractStateBinaryOperator<DataflowState> getWideningOperator() {
		return mMerge;
	}

	@Override
	public IAbstractStateBinaryOperator<DataflowState> getMergeOperator() {
		return mMerge;
	}

	@Override
	public IAbstractPostOperator<DataflowState, CodeBlock, IProgramVar> getPostOperator() {
		return mPost;
	}

	@Override
	public int getDomainPrecision() {
		throw new UnsupportedOperationException("this domain has no precision");
	}

	private final class DataflowMergeOperator implements IAbstractStateBinaryOperator<DataflowState> {

		@Override
		public DataflowState apply(final DataflowState first, final DataflowState second) {
			final DataflowState rtr = first.union(second);
			if (mLogger.isDebugEnabled()) {
				final StringBuilder sb = new StringBuilder();
				sb.append("merge(");
				sb.append(first.toLogString());
				sb.append(',');
				sb.append(second.toLogString());
				sb.append(") = ");
				sb.append(rtr.toLogString());
				mLogger.debug(sb);
			}
			return rtr;
		}
	}
}
