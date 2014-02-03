/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	DefaultAnnotations.java created on Mar 7, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model.annotation;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

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
	private transient Map<String, Object> backingMap;

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
		if (backingMap == null) {
			backingMap = new AbstractMap<String, Object>() {
				private Set<Entry<String, Object>> m_EntrySet = new AbstractSet<Entry<String, Object>>() {

					private String[] m_AttribFields = getFieldNames();

					@Override
					public Iterator<Entry<String, Object>> iterator() {
						return new Iterator<Entry<String, Object>>() {
							int fieldCount = 0;

							@Override
							public boolean hasNext() {
								return fieldCount < m_AttribFields.length;
							}

							@Override
							public Entry<String, Object> next() {
								String field = m_AttribFields[fieldCount++];
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
						return m_AttribFields.length;
					}
				};

				@Override
				public Set<Entry<String, Object>> entrySet() {
					return m_EntrySet;
				}
			};
		}
		return backingMap;
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
