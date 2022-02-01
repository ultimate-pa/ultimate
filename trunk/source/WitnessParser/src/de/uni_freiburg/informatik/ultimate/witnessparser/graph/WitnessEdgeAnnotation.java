/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.witnessparser.Activator;

public class WitnessEdgeAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String KEY = Activator.PLUGIN_ID + "_Edge";

	@Visualizable
	private final Boolean mCondition;
	@Visualizable
	private final String mEnterFrom;
	@Visualizable
	private final String mReturnFrom;
	@Visualizable
	private final String mTokens;
	@Visualizable
	private final String mAssumption;
	@Visualizable
	private final Boolean mEnterLoopHead;

	public WitnessEdgeAnnotation(final String condition, final String enterLoopHead, final String enterFrom,
			final String returnFrom, final String tokens, final String assumption) {
		this(convertOrFail(condition), convertOrFail(enterLoopHead), enterFrom, returnFrom, tokens, assumption);
	}

	public WitnessEdgeAnnotation(final Boolean condition, final Boolean enterLoopHead, final String enterFrom,
			final String returnFrom, final String tokens, final String assumption) {
		mCondition = condition;
		mEnterFrom = enterFrom;
		mEnterLoopHead = enterLoopHead;
		mReturnFrom = returnFrom;
		mTokens = tokens;
		mAssumption = assumption;
	}

	public Boolean getCondition() {
		return mCondition;
	}

	public String getEnterFrom() {
		return mEnterFrom;
	}

	public String getReturnFrom() {
		return mReturnFrom;
	}

	public String getTokens() {
		return mTokens;
	}

	public String getAssumption() {
		return mAssumption;
	}

	public Boolean getEnterLoopHead() {
		return mEnterLoopHead;
	}

	public boolean isEmpty() {
		return getCondition() == null && getEnterFrom() == null && getReturnFrom() == null && getTokens() == null
				&& getAssumption() == null && getEnterLoopHead() == null;
	}

	public void annotate(final IElement elem) {
		if (elem instanceof WitnessEdge) {
			annotate((WitnessEdge) elem);
		}
	}

	public void annotate(final WitnessEdge elem) {
		elem.getPayload().getAnnotations().put(KEY, this);
	}

	public static WitnessEdgeAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (WitnessEdgeAnnotation) a);
	}

	@SuppressWarnings("squid:S2447")
	private static Boolean convertOrFail(final String boolStr) {
		if (boolStr == null) {
			return null;
		}
		if ("true".equalsIgnoreCase(boolStr)) {
			return Boolean.TRUE;
		}
		if ("false".equalsIgnoreCase(boolStr)) {
			return Boolean.FALSE;
		}
		throw new IllegalArgumentException("A boolean attribute has to be true or false");
	}
}
