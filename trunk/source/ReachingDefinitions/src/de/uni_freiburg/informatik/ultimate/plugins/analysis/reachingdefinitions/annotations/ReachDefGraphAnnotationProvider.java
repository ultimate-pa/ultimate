/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class ReachDefGraphAnnotationProvider<T extends ReachDefBaseAnnotation> implements IAnnotationProvider<T> {

	private static final String sDefaultKey = "Default";
	public static final String sAnnotationName = "ReachingDefinition";

	private final String mAnnotationSuffix;

	private final HashSet<String> mKeys;

	public ReachDefGraphAnnotationProvider(String annotationSuffix) {
		mAnnotationSuffix = annotationSuffix;
		mKeys = new HashSet<>();
		mKeys.add(sDefaultKey);
	}

	@Override
	public T getAnnotation(IElement element) {
		return getAnnotation(element, sDefaultKey);
	}

	@Override
	public void annotate(IElement node, T annotation) {
		annotate(node, annotation, sDefaultKey);
	}

	@SuppressWarnings("unchecked")
	@Override
	public T getAnnotation(IElement element, String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		final String key = sAnnotationName + " " + uniqueId;
		if (mAnnotationSuffix == null) {
			return (T) element.getPayload().getAnnotations().get(key);
		} else {
			return (T) element.getPayload().getAnnotations().get(key + " " + mAnnotationSuffix);
		}
	}

	@Override
	public void annotate(IElement node, T annotation, String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		mKeys.add(uniqueId);
		final String key = sAnnotationName + " " + uniqueId;
		if (mAnnotationSuffix == null) {
			node.getPayload().getAnnotations().put(key, annotation);
		} else {
			node.getPayload().getAnnotations().put(key + " " + mAnnotationSuffix, annotation);
		}
	}

	@Override
	public List<T> getAllAnnotations(IElement element) {
		final List<T> rtr = new ArrayList<>();
		for(final String key : mKeys){
			final T annot = getAnnotation(element, key);
			if(annot != null){
				rtr.add(annot);
			}
		}
		return rtr;
	}

}
