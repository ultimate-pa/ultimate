/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model.models;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Helper methods for Ultimate models.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ModelUtils {

	private ModelUtils() {
		// do not instantiate utility class.
	}

	/**
	 * Takes annotations from one {@link IElement} (if any) and adds them to another {@link IElement}. This is a shallow
	 * copy.
	 *
	 * @param oldE
	 *            old {@link IElement} to take annotations from.
	 * @param newE
	 *            new {@link IElement} to add annotations to.
	 */
	public static void copyAnnotations(final IElement oldE, final IElement newE) {
		copyAnnotationsFiltered(oldE, newE, a -> true);
	}

	/**
	 * Collects all annotations annotated to a collection of {@link IElement}s and annotates them to a new
	 * {@link IElement}.
	 *
	 * Throws an exception if annotations would be lost.
	 *
	 * @param oldElem
	 *            a collection of {@link IElement}s
	 * @param newElem
	 *            the IElement to which the annotations should be annotated
	 */
	public static void mergeAnnotations(final Collection<? extends IElement> oldElem, final IElement newElem) {
		if (oldElem == null || newElem == null) {
			return;
		}

		final List<Entry<String, IAnnotations>> oldElemAnnots = oldElem.stream().map(ModelUtils::getAnnotations)
				.filter(a -> a != null).flatMap(a -> a.entrySet().stream()).collect(Collectors.toList());
		final Map<String, IAnnotations> newElemAnnots = newElem.getPayload().getAnnotations();
		for (final Entry<String, IAnnotations> oldElemAnnot : oldElemAnnots) {

			final String key = oldElemAnnot.getKey();
			final IAnnotations oldNewElemAnnot = newElemAnnots.get(key);
			if (oldNewElemAnnot != null) {
				final IAnnotations mergedAnnotation = oldNewElemAnnot.merge(oldElemAnnot.getValue());
				if (mergedAnnotation != null) {
					// if we get null, the annotation wants to be deleted
					newElemAnnots.put(key, mergedAnnotation);
				}
			} else {
				newElemAnnots.put(key, oldElemAnnot.getValue());
			}
		}
	}

	public static void mergeAnnotations(final IElement newElem, final IElement... oldElements) {
		if (oldElements == null || oldElements.length == 0) {
			return;
		}
		mergeAnnotations(Arrays.asList(oldElements), newElem);
	}

	/**
	 * Takes annotations from one {@link IElement} that are assignable from <code>annotation</code> and adds them to
	 * another {@link IElement}. This is a shallow copy.
	 *
	 * @param oldE
	 *            old {@link IElement} to take annotations from
	 * @param newE
	 *            new {@link IElement} to add annotations to
	 * @param annotation
	 *            the type of annotation that should be copied
	 */
	public static <E extends IAnnotations> void copyAnnotations(final IElement oldE, final IElement newE,
			final Class<E> annotation) {
		if (oldE == null || newE == null || annotation == null) {
			return;
		}
		copyAnnotationsFiltered(oldE, newE, a -> annotation.isAssignableFrom(a.getClass()));
	}

	/**
	 * Takes annotations from one {@link IElement} (if any) and adds them to another {@link IElement} if they are not
	 * assignable from one of the types specified in clazzes. This is a shallow copy.
	 *
	 * @param oldE
	 *            old {@link IElement} to take annotations from.
	 * @param newE
	 *            new {@link IElement} to add annotations to.
	 */
	public static void copyAnnotationsExcept(final IElement oldE, final IElement newE, final Class<?>... clazzes) {
		if (clazzes == null || clazzes.length == 0) {
			copyAnnotations(oldE, newE);
			return;
		}
		copyAnnotationsFiltered(oldE, newE,
				a -> !Arrays.stream(clazzes).anyMatch(b -> b.isAssignableFrom(a.getClass())));
	}

	private static void copyAnnotationsFiltered(final IElement oldE, final IElement newE,
			final Predicate<IAnnotations> filter) {
		final Map<String, IAnnotations> oldAnnots = getAnnotations(oldE);
		if (oldAnnots == null) {
			return;
		}
		final Map<String, IAnnotations> newAnnots = newE.getPayload().getAnnotations();
		for (final Entry<String, IAnnotations> oldAnnot : oldAnnots.entrySet()) {
			if (!filter.test(oldAnnot.getValue())) {
				continue;
			}

			final IAnnotations replacedValue = newAnnots.put(oldAnnot.getKey(), oldAnnot.getValue());
			if (replacedValue == null) {
				continue;
			}
			// we would overwrite old annotations, so we merge instead
			final IAnnotations mergedAnnot = replacedValue.merge(oldAnnot.getValue());
			if (mergedAnnot != null) {
				newAnnots.put(oldAnnot.getKey(), mergedAnnot);
			}
		}
	}

	/**
	 * Applies all annotations of <code>elem</code> (if any) to a provided {@link Consumer}.
	 *
	 * @param elem
	 *            The element from which annotations should be taken.
	 * @param funConsumer
	 *            The consumer instance.
	 */
	public static void consumeAnnotations(final IElement elem,
			final Consumer<Entry<String, IAnnotations>> funConsumer) {
		final Map<String, IAnnotations> annots = getAnnotations(elem);
		if (annots == null) {
			return;
		}
		annots.entrySet().stream().forEach(funConsumer);
	}

	/**
	 * Get some {@link IAnnotations} implementer from an {@link IElement} with the matching key if present.
	 *
	 * @param node
	 *            The {@link IElement} instance which has the annotation
	 * @param key
	 *            The key of the annotation
	 * @param funCast
	 *            A function that casts IAnnotations to the desired type
	 * @return An instance of a type implementing {@link IAnnotations} and annotated to <code>node</code>
	 */
	public static <T extends IAnnotations> T getAnnotation(final IElement node, final String key,
			final Function<IAnnotations, T> funCast) {
		if (node == null) {
			return null;
		}
		if (node.hasPayload()) {
			final IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				final IAnnotations annot = payload.getAnnotations().get(key);
				if (annot != null) {
					return funCast.apply(annot);
				}
			}
		}
		return null;
	}

	/**
	 * @return annotation map of an {@link IElement} without creating an empty map.
	 */
	private static Map<String, IAnnotations> getAnnotations(final IElement elem) {
		if (elem == null) {
			return null;
		}
		if (!elem.hasPayload()) {
			return null;
		}
		final IPayload oldPayload = elem.getPayload();
		if (oldPayload.hasAnnotation()) {
			return oldPayload.getAnnotations();
		}
		return null;
	}
}
