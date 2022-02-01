/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * Annotation for statements that (possibly) enter a loop. This marks the following statements.
 * <ul>
 * <li>assume statements that result from a while-loop condition being true,
 * <li>goto-statements that existed before unstructuring
 * </ul>
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class LoopExitAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String KEY = LoopExitAnnotation.class.getName();

	@Visualizable
	private final LoopExitType mType;

	public LoopExitAnnotation(final LoopExitType loopEntryType) {
		mType = loopEntryType;
	}

	public LoopExitType getLoopExitType() {
		return mType;
	}

	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	public static LoopExitAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (LoopExitAnnotation) a);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof LoopExitAnnotation) {
			final LoopExitAnnotation otherLoopExit = (LoopExitAnnotation) other;
			if (otherLoopExit.mType.equals(mType)) {
				return this;
			}
			return new LoopExitAnnotation(LoopExitType.UNKNOWN);
		}
		return super.merge(other);
	}

	@Override
	public String toString() {
		return mType.toString();
	}

	public enum LoopExitType {
		BREAK, RETURN, GOTO, WHILE, UNKNOWN
	}
}
