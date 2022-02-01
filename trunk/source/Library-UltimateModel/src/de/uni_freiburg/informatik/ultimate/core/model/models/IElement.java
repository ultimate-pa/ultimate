/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

/**
 * 
 * This interface implements a proxy pattern for IPayload. It is also the root
 * element of the type hierarchy for Ultimate models.
 * 
 * @author dietsch
 * @see IPayload
 */
public interface IElement extends Serializable {

	/**
	 * Returns the current IPayload of the implementation. If this method is
	 * called for the first time, it will initialize a new IPayload object and
	 * return this. All following calls will return the instance that was
	 * created during the first call. In particular, implementers must ensure
	 * that this method never returns null.
	 * 
	 * @return The current IPayload object of the implementation.
	 */
	IPayload getPayload();
	
	/**
	 * Reports if the IPayload object has been initialized. This method should
	 * be used to check whether a IPayload instance exists if one does not want
	 * to create an instance.
	 * 
	 * @return true iff getPayload() returns an already existing instance of
	 *         IPayload, false iff getPayload() will create a new instance and
	 *         save this, thus increasing memory consumption.
	 */
	boolean hasPayload();
}
