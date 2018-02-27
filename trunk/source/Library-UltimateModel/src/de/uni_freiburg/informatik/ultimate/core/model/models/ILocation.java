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
/**
 * 
 */

package de.uni_freiburg.informatik.ultimate.core.model.models;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Defines an area in a text file. Used to specify where an BoogieASTNode is defined.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ILocation extends IAnnotations {

	/**
	 * @return Name of this {@code Location}s file.
	 */
	String getFileName();

	/**
	 * @return Number of line where this {@code Location} begins. -1 if unknown.
	 */
	int getStartLine();

	/**
	 * @return Number of line where this {@code Location} ends. -1 if unknown.
	 */
	int getEndLine();

	/**
	 * @return Number of column where this {@code Location} begins. -1 if unknown.
	 */
	int getStartColumn();

	/**
	 * @return Number of column where this {@code Location} ends. -1 if unknown.
	 */
	int getEndColumn();

	/**
	 * Textual description of the type of specification which is checked here. E.g., "NullPointerException",
	 * "AssertStatement" etc.
	 */
	@Deprecated
	IAnnotations getCheck();

	default void annotate(final IElement node) {
		annotate(node.getPayload());
	}

	default void annotate(final IPayload payload) {
		payload.getAnnotations().put(ILocation.class.getName(), this);
	}

	/**
	 * @return the {@link ILocation} instance annotated to <code>elem</code> or null if there is no such instance of if
	 *         elem is null
	 */
	static ILocation getAnnotation(final IElement elem) {
		return ModelUtils.getAnnotation(elem, ILocation.class.getName(), a -> (ILocation) a);
	}

}
