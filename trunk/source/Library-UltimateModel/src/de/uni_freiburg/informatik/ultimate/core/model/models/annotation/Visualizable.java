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
package de.uni_freiburg.informatik.ultimate.core.model.models.annotation;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 *
 * Types that implement {@link IElement} can mark instance fields and methods with this attribute. If a member is
 * marked, Ultimate's debug visualization will display the name of the field or the return value of the method along
 * with its value in the NodeView.
 *
 * The value is obtained by calling {@link #toString()} on the field if it is not null, or by invoking
 * {@link String#valueOf(Object)}. For a method, it is assumed that it does not take any arguments. Its return value is
 * then treated like a field.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface Visualizable {
	// no methods needed, just for marking
}
