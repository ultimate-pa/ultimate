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

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class AnnotatingRcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>, LOCATION>
		extends BaseRcfgAbstractStateStorageProvider<STATE, LOCATION> {

	private static int sSuffix;
	private final String mSuffix;

	public AnnotatingRcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<STATE> mergeOperator,
			IUltimateServiceProvider services, ITransitionProvider<CodeBlock, LOCATION> transProvider) {
		super(mergeOperator, services, transProvider);
		mSuffix = String.valueOf(sSuffix++);
	}

	protected Deque<STATE> getStates(LOCATION node) {
		assert node != null;
		assert node instanceof IElement : "Cannot persist states for locations that do not support payloads";
		final IElement elem = (IElement) node;
		AbsIntAnnotation<STATE> rtr = AbsIntAnnotation.getAnnotation(elem, mSuffix);
		if (rtr == null) {
			rtr = new AbsIntAnnotation<STATE>();
			rtr.annotate(elem, mSuffix);
		}
		return rtr.mStates;
	}

	private static final class AbsIntAnnotation<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			extends ModernAnnotations {

		private static final String KEY = AbsIntAnnotation.class.getSimpleName();
		private static final long serialVersionUID = 1L;

		@Visualizable
		private final Deque<STATE> mStates;

		private AbsIntAnnotation() {
			mStates = new ArrayDeque<>();
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
	public BaseRcfgAbstractStateStorageProvider<STATE, LOCATION> create() {
		return new AnnotatingRcfgAbstractStateStorageProvider<STATE, LOCATION>(getMergeOperator(), getServices(),
				getTransitionProvider());
	}
}
