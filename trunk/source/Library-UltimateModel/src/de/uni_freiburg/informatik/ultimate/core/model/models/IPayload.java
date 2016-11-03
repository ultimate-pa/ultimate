/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.io.Serializable;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * This interface describes all information contained by an implementation of {@link IElement}.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public interface IPayload extends Serializable {

	/**
	 * Get a two-dimensional {@link Map} containing {@link IAnnotations}. Initializes annotations automatically if not
	 * already initialized.
	 * 
	 * @return the {@link Map} containing the {@link IAnnotations} of this payload.
	 */
	Map<String, IAnnotations> getAnnotations();

	/**
	 * @return an {@link ILocation} instance describing which part of the input is described by this {@link IPayload}.
	 */
	@Deprecated
	ILocation getLocation();

	/**
	 * Returns true if the annotation map is already initialized and contains elements. Returns false if the annotations
	 * are not initialized or contain no elements. Should be used instead of a direct null test of the
	 * {@link #getAnnotations()} method to prevent unnecessary initialization.
	 * 
	 * @return true if the annotation map is already initialized and contains elements. Returns false if the annotations
	 *         are not initialized or contain no elements.
	 */
	boolean hasAnnotation();

	/**
	 * Returns true if this {@link IPayload} instance has a {@link ILocation}. Should be used instead of a direct null
	 * test of the {@link #getLocation()} method to prevent unnecessary initialization.
	 * 
	 * @return true iff this {@link IPayload} has a {@link ILocation} instance, false otherwise.
	 */
	@Deprecated
	boolean hasLocation();

	/**
	 * Overwrites the {@link ILocation} attached to this {@link IPayload} with <code>loc</code>.
	 * 
	 * @deprecated Should not be used anymore because {@link IPayload} should become immutable.
	 */
	@Deprecated
	void setLocation(ILocation loc);
}
