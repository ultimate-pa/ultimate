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
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.Map;
import java.util.function.IntPredicate;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

/**
 * An annotation used to mark CFG edges that are the beginning or end of an atomic block, in the sense of SV-COMP's
 * __VERIFIER_ATOMIC_* feature or in the sense of "atomic { }" statements in our Boogie dialect.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
// TODO Matthias 2024-08-25: Class may become again package private after RCFGBuilder was deleted
final public class AtomicBlockInfo extends ModernAnnotations {

	private static final long serialVersionUID = -8370873908642083605L;

	private static final int START_DELTA = 1;
	private static final int END_DELTA = -1;

	// Difference of number of atomic blocks opened by the annotated edge and number of atomic blocks closed by the
	// annotated edge. Hence, positive numbers indicate the start of an atomic block, negative numbers the end, and zero
	// indicates a complete atomic block.
	private final int mDelta;

	private AtomicBlockInfo(final int delta) {
		mDelta = delta;
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		// We use the default merging behaviour, i.e., merging is not supported.
		// This annotation should only appear temporarily within CfgBuilder.
		// It is up to CfgBuilder to make sure it never attempts to merge two instances of this annotation.
		//
		// It does not make sense to define merging here, as the correct behaviour depends on the context, e.g. whether
		// edges are composed sequentially (deltas are summed) or in parallel (deltas of all parallel edges must be the
		// same as each other, and the same as the delta of the result).
		return super.merge(other);
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return Map.of("delta", mDelta);
	}

	@Override
	public String toString() {
		return AtomicBlockInfo.class.getSimpleName() + "(" + (mDelta > 0 ? "+" : "") + mDelta + ")";
	}

	/**
	 * Determines if the given element (an edge) is annotated as start of an atomic block.
	 *
	 * Note that an edge can be the start of an atomic block or the end, but not both.
	 *
	 * @param edge
	 *            The edge whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks the beginning of an atomic block.
	 */
	public static boolean isStartOfAtomicBlock(final IIcfgTransition<?> edge) {
		return hasAnnotatedDelta(edge, d -> d > 0);
	}

	/**
	 * Determines if the given element (an edge) is annotated as end of an atomic block.
	 *
	 * Note that an edge can be the start of an atomic block or the end, but not both.
	 *
	 * @param edge
	 *            The edge whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks the end of an atomic block.
	 */
	public static boolean isEndOfAtomicBlock(final IIcfgTransition<?> edge) {
		return hasAnnotatedDelta(edge, d -> d < 0);
	}

	/**
	 * Determines if the given element (an edge) is annotated as the result of a complete atomic block composition.
	 *
	 * @param edge
	 *            The edge whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks a complete atomic block.
	 */
	public static boolean isCompleteAtomicBlock(final IIcfgTransition<?> edge) {
		return hasAnnotatedDelta(edge, d -> d == 0);
	}

	/**
	 * Marks the given element (an edge) as the beginning of an atomic block.
	 *
	 * @param element
	 *            The edge to be marked.
	 */
	public static void addBeginAnnotation(final IIcfgTransition<?> edge) {
		addAnnotation(edge, START_DELTA);
	}

	/**
	 * Marks the given element (an edge) as the end of an atomic block.
	 *
	 * @param element
	 *            The edge to be marked.
	 */
	public static void addEndAnnotation(final IIcfgTransition<?> edge) {
		addAnnotation(edge, END_DELTA);
	}

	/**
	 * Marks the given element (an edge) as the result of a complete atomic block composition.
	 *
	 * @param element
	 *            The edge to be marked.
	 */
	public static void addCompleteAnnotation(final IIcfgTransition<?> edge) {
		addAnnotation(edge, 0);
	}

	/**
	 * Removes any {@link AtomicBlockInfo} annotation, if present.
	 *
	 * @param element
	 *            The edge from which annotations shall be removed.
	 */
	public static void removeAnnotation(final IIcfgTransition<?> edge) {
		edge.getPayload().getAnnotations().remove(AtomicBlockInfo.class.getName());
	}

	static boolean hasAnnotation(final IIcfgTransition<?> edge) {
		return ModelUtils.getAnnotation(edge, AtomicBlockInfo.class) != null;
	}

	static int getAnnotatedDelta(final IIcfgTransition<?> edge) {
		final AtomicBlockInfo annotation = ModelUtils.getAnnotation(edge, AtomicBlockInfo.class);
		if (annotation != null) {
			return annotation.mDelta;
		}
		return 0;
	}

	static void mergeSequential(final IIcfgTransition<?> first, final IIcfgTransition<?> second,
			final IIcfgTransition<?> merged) {
		final var mergedAnnotation = mergeSequential(ModelUtils.getAnnotation(first, AtomicBlockInfo.class),
				ModelUtils.getAnnotation(second, AtomicBlockInfo.class));
		if (mergedAnnotation != null) {
			addAnnotation(merged, mergedAnnotation);
		}
	}

	private static AtomicBlockInfo mergeSequential(final AtomicBlockInfo first, final AtomicBlockInfo second) {
		if (first == null) {
			return second;
		}
		if (second == null) {
			return first;
		}
		return new AtomicBlockInfo(first.mDelta + second.mDelta);
	}

	private static boolean hasAnnotatedDelta(final IIcfgTransition<?> edge, final IntPredicate condition) {
		final AtomicBlockInfo annotation = ModelUtils.getAnnotation(edge, AtomicBlockInfo.class);
		if (annotation != null) {
			return condition.test(annotation.mDelta);
		}
		return false;
	}

	static void addAnnotation(final IIcfgTransition<?> edge, final int delta) {
		addAnnotation(edge, new AtomicBlockInfo(delta));
	}

	private static void addAnnotation(final IIcfgTransition<?> edge, final AtomicBlockInfo annotation) {
		final var previous = ModelUtils.getAnnotation(edge, AtomicBlockInfo.class);
		if (previous != null) {
			throw new UnsupportedOperationException(
					"Incompatible atomic block annotation: " + previous.mDelta + " and " + annotation.mDelta);
		}
		edge.getPayload().getAnnotations().put(AtomicBlockInfo.class.getName(), annotation);
	}
}
