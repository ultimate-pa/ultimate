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

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Visualizable;

public class WitnessEdgeAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = Activator.PLUGIN_ID + "_Edge";

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

	public WitnessEdgeAnnotation(String condition, String enterFrom, String returnFrom, String tokens, String assumption) {
		this(condition != null ? Boolean.valueOf(condition) : null, enterFrom, returnFrom, tokens, assumption);
	}

	public WitnessEdgeAnnotation(Boolean condition, String enterFrom, String returnFrom, String tokens,
			String assumption) {
		mCondition = condition;
		mEnterFrom = enterFrom;
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

	public boolean isEmpty() {
		return getCondition() == null && getEnterFrom() == null && getReturnFrom() == null && getTokens() == null
				&& getAssumption() == null;
	}

	public void annotate(IElement elem) {
		if (elem instanceof WitnessEdge) {
			annotate((WitnessEdge) elem);
		}
	}

	public void annotate(WitnessEdge elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static WitnessEdgeAnnotation getAnnotation(IElement elem) {
		if (elem instanceof WitnessEdge) {
			return getAnnotation((WitnessEdge) elem);
		}
		return null;
	}

	public static WitnessEdgeAnnotation getAnnotation(WitnessEdge elem) {
		if (elem.hasPayload()) {
			final IPayload payload = elem.getPayload();
			if (payload.hasAnnotation()) {
				final IAnnotations annot = payload.getAnnotations().get(sKey);
				if (annot != null) {
					return (WitnessEdgeAnnotation) annot;
				}
			}
		}
		return null;
	}
}
