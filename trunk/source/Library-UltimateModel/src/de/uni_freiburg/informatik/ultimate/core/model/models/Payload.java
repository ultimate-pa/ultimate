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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * A concrete implementation of the {@link IPayload} interface. The payload contains all information carried by a node.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class Payload implements IPayload {

	private static final long serialVersionUID = 9150283961581614549L;
	private ILocation mLocation;
	private Map<String, IAnnotations> mAnnotations;

	public Payload() {
		this(null);
	}

	public Payload(final ILocation loc) {
		mLocation = loc;
	}

	@Override
	public Map<String, IAnnotations> getAnnotations() {
		if (mAnnotations == null) {
			mAnnotations = new HashMap<>();
		}
		return mAnnotations;
	}

	@Override
	public ILocation getLocation() {
		return mLocation;
	}

	@Override
	public boolean hasAnnotation() {
		if (mAnnotations == null) {
			return false;
		}
		return !mAnnotations.isEmpty();
	}

	@Override
	public boolean hasLocation() {
		return (mLocation != null);
	}

	@Override
	public String toString() {
		if (hasLocation()) {
			return getLocation().toString();
		}
		return super.toString();
	}

	@Override
	public void setLocation(final ILocation loc) {
		mLocation = loc;
	}
}
