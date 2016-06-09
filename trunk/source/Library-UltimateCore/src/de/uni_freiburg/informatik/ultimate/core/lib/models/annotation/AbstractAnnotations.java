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
 * File:	DefaultAnnotations.java created on Mar 7, 2010 by Björn Buchhold
 *
 */

package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * DefaultAnnotations
 * 
 * @author Björn Buchhold
 * 
 */
public abstract class AbstractAnnotations implements IAnnotations {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -3930174445763628926L;

	/**
	 * The backing map. Cached on first call.
	 */
	private transient Map<String, Object> mBackingMap;

	/**
	 * Returns the array of keys of this annotation. Subclasses must override
	 * this to specify which fields are available. May not return null!
	 */
	protected abstract String[] getFieldNames();

	/**
	 * Returns for a key in the annotation the corresponding object. Subclasses
	 * must override this to return the value of the corresponding field.
	 */
	protected abstract Object getFieldValue(String field);

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		if (mBackingMap == null) {
			mBackingMap = new AbstractMap<String, Object>() {
				private final Set<Entry<String, Object>> mEntrySet = new AbstractSet<Entry<String, Object>>() {

					private final String[] mAttribFields = getFieldNames();

					@Override
					public Iterator<Entry<String, Object>> iterator() {
						return new Iterator<Entry<String, Object>>() {
							int fieldCount = 0;

							@Override
							public boolean hasNext() {
								return fieldCount < mAttribFields.length;
							}

							@Override
							public Entry<String, Object> next() {
								final String field = mAttribFields[fieldCount++];
								return new AbstractMap.SimpleImmutableEntry<String, Object>(field, getFieldValue(field));
							}

							@Override
							public void remove() {
								throw new UnsupportedOperationException();
							}
						};
					}

					@Override
					public int size() {
						return mAttribFields.length;
					}
				};

				@Override
				public Set<Entry<String, Object>> entrySet() {
					return mEntrySet;
				}
			};
		}
		return mBackingMap;
	}

	/**
	 * Return a string representation of this class. The default implementation
	 * will print the class name of the annotation followed by colon and the
	 * attribute map.
	 */
	@Override
	public String toString() {
		return getClass().toString() + ":" + getAnnotationsAsMap().toString();
	}

}
