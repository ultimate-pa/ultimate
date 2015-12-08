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
import java.util.ArrayList;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class AnnotatingRcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
		extends BaseRcfgAbstractStateStorageProvider<STATE> {

	private static int sSuffix;
	private final String mSuffix;

	public AnnotatingRcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<STATE> mergeOperator,
			IUltimateServiceProvider services) {
		super(mergeOperator, services);
		mSuffix = String.valueOf(sSuffix++);
	}

	protected Deque<Pair<CodeBlock, STATE>> getStates(RCFGNode node) {
		assert node != null;
		AbsIntAnnotation<STATE> rtr = AbsIntAnnotation.getAnnotation(node, mSuffix);
		if (rtr == null) {
			rtr = new AbsIntAnnotation<STATE>();
			rtr.annotate(node, mSuffix);
		}
		return rtr.mStates;
	}

	private static final class AbsIntAnnotation<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			extends AbstractAnnotations {

		private static final String KEY = AbsIntAnnotation.class.getSimpleName();
		private static final String[] FIELD_NAMES = new String[] { "States" };
		private static final long serialVersionUID = 1L;
		private final Deque<Pair<CodeBlock, STATE>> mStates;

		private AbsIntAnnotation() {
			mStates = new ArrayDeque<>();
		}

		@Override
		protected String[] getFieldNames() {
			return FIELD_NAMES;
		}

		@Override
		protected Object getFieldValue(String field) {
			if (FIELD_NAMES[0].equals(field)) {
				// states
				final ArrayList<String> rtr = new ArrayList<>();
				for (final Pair<CodeBlock, STATE> entry : mStates) {
					rtr.add(new StringBuilder().append("[").append(entry.getSecond().hashCode()).append("] ")
							.append(entry.getSecond().toLogString()).append(" (from ")
							.append(entry.getFirst().getPrettyPrintedStatements()).append(")").toString());
				}
				return rtr.toArray(new String[rtr.size()]);
			}
			return null;
		}

		public void annotate(IElement elem, String suffix) {
			elem.getPayload().getAnnotations().put(KEY + suffix, this);
		}

		@SuppressWarnings("unchecked")
		public static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>> AbsIntAnnotation<STATE> getAnnotation(
				IElement elem, String suffix) {
			if (!elem.hasPayload()) {
				return null;
			}
			if (!elem.getPayload().hasAnnotation()) {
				return null;
			}
			return (AbsIntAnnotation<STATE>) elem.getPayload().getAnnotations().get(KEY + suffix);
		}
	}

	@Override
	public IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, ProgramPoint> createStorage() {
		return new AnnotatingRcfgAbstractStateStorageProvider<STATE>(getMergeOperator(), getServices());
	}
}
