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

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessGraphAnnotation extends ModernAnnotations {

	public enum WitnessType {
		TRUE_WITNESS, FALSE_WITNESS
	}

	private static final long serialVersionUID = 1L;
	private static final String sKey = Activator.PLUGIN_ID + "_Graph";

	@Visualizable
	private final String mSourceCodeLanguage;

	@Visualizable
	private final WitnessType mType;

	public WitnessGraphAnnotation(final String sourceodelang, final WitnessType type) {
		mSourceCodeLanguage = sourceodelang;
		mType = type;
	}

	public void annotate(IElement node) {
		if (node instanceof WitnessNode) {
			annotate((WitnessNode) node);
		}
	}

	public void annotate(WitnessNode node) {
		node.getPayload().getAnnotations().put(sKey, this);
	}

	public static WitnessGraphAnnotation getAnnotation(IElement node) {
		if (node instanceof WitnessNode) {
			return getAnnotation((WitnessNode) node);
		}
		return null;
	}

	public static WitnessGraphAnnotation getAnnotation(WitnessNode node) {
		if (node.hasPayload()) {
			final IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				final IAnnotations annot = payload.getAnnotations().get(sKey);
				if (annot != null) {
					return (WitnessGraphAnnotation) annot;
				}
			}
		}
		return null;
	}

	public String getSourceCodeLanguage() {
		return mSourceCodeLanguage;
	}

	public WitnessType getWitnessType() {
		return mType;
	}
}
