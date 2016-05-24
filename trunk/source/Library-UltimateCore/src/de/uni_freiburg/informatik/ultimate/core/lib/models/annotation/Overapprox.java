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

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Annotation for transition (e.g., CodeBlock) that indicates that it was not
 * build by a semantics preserving translation but by an overapproximation.
 * This allows model checkers to report <i>unknown</i> instead of <i>unsafe</i>
 * for traces that contain elements with this annotation.
 */
public class Overapprox extends AbstractAnnotations {
	
	public static final String s_REASON_FOR_OVERAPPROXIMATION = "Reason for overapproximation";
	public static final String s_LOCATION_MAPPING = "Location mapping";
	
	public static final String BITVEC = "bitvector operation";
	public static final String FUNC_POINTER = "call of function pointer";
	
	
	public static final String getIdentifier() {
		return Overapprox.class.getName();
	}
	
	private final Map<String, ILocation> mReason2Loc;
	
	public Overapprox(Map<String, ILocation> reason2Loc) {
		mReason2Loc = reason2Loc;
	}
	
	public Overapprox(String reason, ILocation loc) {
        mReason2Loc = Collections.singletonMap(reason, loc);
    }

	private static final long serialVersionUID = -575969312624287029L;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		s_REASON_FOR_OVERAPPROXIMATION, s_LOCATION_MAPPING
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field.equals(s_REASON_FOR_OVERAPPROXIMATION))
			return mReason2Loc.keySet();
		else if (field.equals(s_LOCATION_MAPPING))
			return mReason2Loc;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

}
