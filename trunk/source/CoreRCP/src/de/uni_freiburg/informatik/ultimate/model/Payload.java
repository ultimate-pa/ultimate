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
package de.uni_freiburg.informatik.ultimate.model;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * A concrete implementation of the {@link IPayload} interface. The payload
 * contains all informations carried by a node.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class Payload implements IPayload {

	private static final long serialVersionUID = 9150283961581614549L;
	protected ILocation mLocation;
	protected String mName;
	protected UltimateUID mID;
	protected HashMap<String, IAnnotations> mAnnotations;
	protected boolean mIsValue;

	public Payload() {
		mIsValue = false;
	}

	public Payload(ILocation loc, String name) {
		this();
		mLocation = loc;
		mName = name;
	}

	public Payload(ILocation loc, String name, boolean isValue) {
		this();
		mLocation = loc;
		mName = name;
		mIsValue = isValue;
	}

	public HashMap<String, IAnnotations> getAnnotations() {
		if (mAnnotations == null) {
			mAnnotations = new HashMap<String, IAnnotations>();
		}
		return mAnnotations;
	}

	public UltimateUID getID() {
		if (mID == null) {
			mID = new UltimateUID();
		}
		return mID;
	}

	public ILocation getLocation() {
		return mLocation;
	}

	public String getName() {
		if (mName == null) {
			return "";
		}
		return mName;
	}

	public void setAnnotations(HashMap<String, IAnnotations> annotations) {
		mAnnotations = annotations;

	}

	public void setLocation(ILocation loc) {
		mLocation = loc;
	}

	public void setName(String name) {
		mName = name;
	}

	public String toString() {
		return getName();
	}

	public boolean hasAnnotation() {
		if (mAnnotations == null) {
			return false;
		}
		return !mAnnotations.isEmpty();
	}

	public boolean hasLocation() {
		return (mLocation != null);
	}

	public boolean hasID() {
		return (mID != null);
	}

	public boolean hasName() {
		return (mName != null);
	}

	public boolean isValue() {
		return mIsValue;
	}

}
