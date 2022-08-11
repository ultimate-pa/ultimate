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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * An annotation used to mark CFG locations that are the beginning or end of an atomic block, in the sense of SV-COMP's
 * __VERIFIER_ATOMIC_* feature or in the sense of "atomic { }" statements in our Boogie dialect.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class AtomicBlockInfo extends ModernAnnotations {

	private static final long serialVersionUID = -8370873908642083605L;

	private final boolean mBeginAtomic;
	private final boolean mEndAtomic;

	private AtomicBlockInfo(final boolean beginAtomic, final boolean endAtomic) {
		mBeginAtomic = beginAtomic;
		mEndAtomic = endAtomic;
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof AtomicBlockInfo) {
			final boolean isBegin = ((AtomicBlockInfo) other).mBeginAtomic || mBeginAtomic;
			final boolean isEnd = ((AtomicBlockInfo) other).mEndAtomic || mEndAtomic;
			return new AtomicBlockInfo(isBegin, isEnd);
		}
		return super.merge(other);
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		final Map<String, Object> map = new HashMap<>();
		map.put("Begin Block", mBeginAtomic);
		map.put("End Block", mEndAtomic);
		return map;
	}

	/**
	 * Determines if the given element (resp., location) is annotated as start of an atomic block.
	 *
	 * Note that a location can be both the start of an atomic block and the end of a (preceding) atomic block.
	 *
	 * @param element
	 *            The element whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks the beginning of an atomic block.
	 */
	public static boolean isStartOfAtomicBlock(final IElement element) {
		final AtomicBlockInfo annotation =
				ModelUtils.getAnnotation(element, AtomicBlockInfo.class.getName(), AtomicBlockInfo.class::cast);
		if (annotation != null) {
			return annotation.mBeginAtomic;
		}
		return false;
	}

	/**
	 * Determines if the given element (resp., location) is annotated as end of an atomic block.
	 *
	 * Note that a location can be both the end of an atomic block and the start of a (succeeding) atomic block.
	 *
	 * @param element
	 *            The element whose annotation is examined.
	 * @return true if there is an {@link AtomicBlockInfo} annotation that marks the end of an atomic block.
	 */
	public static boolean isEndOfAtomicBlock(final IElement element) {
		final AtomicBlockInfo annotation =
				ModelUtils.getAnnotation(element, AtomicBlockInfo.class.getName(), AtomicBlockInfo.class::cast);
		if (annotation != null) {
			return annotation.mEndAtomic;
		}
		return false;
	}

	/**
	 * Marks the given element (typically, a location) as the beginning of an atomic block.
	 *
	 * @param element
	 *            The location to be marked.
	 */
	public static void addBeginAnnotation(final IElement element) {
		final boolean isEnd = isEndOfAtomicBlock(element);
		element.getPayload().getAnnotations().put(AtomicBlockInfo.class.getName(), new AtomicBlockInfo(true, isEnd));
	}

	/**
	 * Marks the given element (typically, a location) as the end of an atomic block.
	 *
	 * @param element
	 *            The location to be marked.
	 */
	public static void addEndAnnotation(final IElement element) {
		final boolean isBegin = isStartOfAtomicBlock(element);
		element.getPayload().getAnnotations().put(AtomicBlockInfo.class.getName(), new AtomicBlockInfo(isBegin, true));
	}
}
