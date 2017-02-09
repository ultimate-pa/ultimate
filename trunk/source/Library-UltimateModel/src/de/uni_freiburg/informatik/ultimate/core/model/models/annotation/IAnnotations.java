/*
 * Copyright (C) 2015 Björn Buchhold
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	IAnnotation.java created on Mar 7, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.model.models.annotation;

import java.io.Serializable;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

/**
 * {@link IAnnotations} is an interface that describes all objects that can be annotated to {@link IElement}s via
 * {@link IPayload}.
 * 
 * @author Björn Buchhold
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public interface IAnnotations extends Serializable {

	/**
	 * Gets the annotations as a string-object mapping for use in output plug-ins.
	 * 
	 * @return the annotations as string-object mapping
	 */
	Map<String, Object> getAnnotationsAsMap();

	/**
	 * Create a new IAnnotations object that contains information from this instance and another one.
	 * 
	 * @param other
	 *            another {@link IAnnotations} instance.
	 * @return A combined {@link IAnnotations} instance.
	 */
	default IAnnotations merge(final IAnnotations other) {
		if (other == null) {
			return this;
		}
		throw new UnmergeableAnnotationsException("Cannot merge " + getClass() + " with " + other.getClass());
	}

	/**
	 * An {@link UnmergeableAnnotationsException} is thrown if two {@link IAnnotations} instances cannot be merged.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public static class UnmergeableAnnotationsException extends RuntimeException {

		private static final long serialVersionUID = 1L;

		public UnmergeableAnnotationsException(final String msg) {
			super(msg);
		}
	}

}
