/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * An annotation used to mark CFG edges that are the beginning or end of an atomic block, in the sense of SV-COMP's
 * __VERIFIER_ATOMIC_* feature or in the sense of "atomic { }" statements in our Boogie dialect.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class AtomicBlockInfo extends ModernAnnotations {

	private static final long serialVersionUID = -8370873908642083605L;

	private enum Type {
		START, END, COMPLETE
	}

	private final Type mType;

	private AtomicBlockInfo(final Type type) {
		mType = type;
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		// We use the default merging behaviour, i.e., merging is not supported.
		// This annotation should only appear temporarily within CfgBuilder.
		// It is up to CfgBuilder to make sure it never attempts to merge two instances of this annotation.
		return super.merge(other);
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return Map.of("type", mType);
	}

	/**
	 * Determines if the given element (an edge) is annotated as start of an atomic block.
	 *
	 * Note that an edge can be the start of an atomic block or the end, but not both.
	 *
	 * @param element
	 *            The element whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks the beginning of an atomic block.
	 */
	public static boolean isStartOfAtomicBlock(final IElement element) {
		return annotationHasType(element, Type.START);
	}

	/**
	 * Determines if the given element (an edge) is annotated as end of an atomic block.
	 *
	 * Note that an edge can be the start of an atomic block or the end, but not both.
	 *
	 * @param element
	 *            The element whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks the end of an atomic block.
	 */
	public static boolean isEndOfAtomicBlock(final IElement element) {
		return annotationHasType(element, Type.END);
	}

	/**
	 * Determines if the given element (an edge) is annotated as the result of a complete atomic block composition.
	 *
	 * @param element
	 *            The element whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks a complete atomic block.
	 */
	public static boolean isCompleteAtomicBlock(final IElement element) {
		return annotationHasType(element, Type.COMPLETE);
	}

	/**
	 * Marks the given element (an edge) as the beginning of an atomic block.
	 *
	 * @param element
	 *            The edge to be marked.
	 */
	public static void addBeginAnnotation(final IElement element) {
		addAnnotation(element, Type.START);
	}

	/**
	 * Marks the given element (an edge) as the end of an atomic block.
	 *
	 * @param element
	 *            The edge to be marked.
	 */
	public static void addEndAnnotation(final IElement element) {
		addAnnotation(element, Type.END);
	}

	/**
	 * Marks the given element (an edge) as the result of a complete atomic block composition.
	 *
	 * @param element
	 *            The edge to be marked.
	 */
	public static void addCompleteAnnotation(final IElement element) {
		addAnnotation(element, Type.COMPLETE);
	}

	/**
	 * Removes any {@link AtomicBlockInfo} annotation, if present.
	 *
	 * @param element
	 *            The edge from which annotations shall be removed
	 */
	public static void removeAnnotation(final IElement element) {
		element.getPayload().getAnnotations().remove(AtomicBlockInfo.class.getName());
	}

	private static boolean annotationHasType(final IElement element, final Type type) {
		final AtomicBlockInfo annotation = ModelUtils.getAnnotation(element, AtomicBlockInfo.class);
		if (annotation != null) {
			return annotation.mType == type;
		}
		return false;
	}

	private static void addAnnotation(final IElement element, final Type type) {
		final var previous = ModelUtils.getAnnotation(element, AtomicBlockInfo.class);
		if (previous != null) {
			throw new UnsupportedOperationException(
					"Incompatible atomic block annotation: " + previous.mType + " and " + type);
		}
		element.getPayload().getAnnotations().put(AtomicBlockInfo.class.getName(), new AtomicBlockInfo(type));
	}
}
