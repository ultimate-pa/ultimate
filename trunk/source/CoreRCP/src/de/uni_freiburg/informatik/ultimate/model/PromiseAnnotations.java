package de.uni_freiburg.informatik.ultimate.model;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Implementation of the annotations interface which backs the map view on a 
 * live map of the variables and functions.
 * 
 * Extending classes should register their methods and variables in the
 * constructor and not overwrite the <code>getAnnotationsAsMap</code> method.
 * @author Juergen Christ
 */
public class PromiseAnnotations implements IAnnotations {
	/**
	 * Serialization stuff.
	 */
	private static final long serialVersionUID = -2274093609960398341L;
	private static interface IPromise {
		Object evaluate(PromiseAnnotations pa);
	}
	private static class MemberPromise implements IPromise {
		Field m_target;
		public MemberPromise(Field f) {
			m_target = f;
			m_target.setAccessible(true);
		}
		public Object evaluate(PromiseAnnotations pa) {
			try {
				return m_target.get(pa);
			} catch (IllegalArgumentException e) {
				e.printStackTrace(System.err);
			} catch (IllegalAccessException e) {
				e.printStackTrace(System.err);
			}
			return null;
		}
	}
	private static class MemfunPromise implements IPromise {
		Method m_target;
		public MemfunPromise(Method ma) {
			m_target = ma;
			m_target.setAccessible(true);
		}
		public Object evaluate(PromiseAnnotations pa) {
			try {
				return m_target.invoke(pa, (Object[])null);
			} catch (IllegalArgumentException e) {
				e.printStackTrace(System.err);
			} catch (IllegalAccessException e) {
				e.printStackTrace(System.err);
			} catch (InvocationTargetException e) {
				e.printStackTrace(System.err);
			}
			return null;
		}
	}
	/**
	 * Backing store for the representation.
	 */
	private Map<String, IPromise> m_rep;
	/**
	 * Default constructor to initialize the internal representation.
	 */
	public PromiseAnnotations() {
		m_rep = new HashMap<String, IPromise>();
	}
	/**
	 * Map a member variable to a key. This variable might have any access
	 * restriction.
	 * @param key     Key used in {{@link #getAnnotationsAsMap()}.
	 * @param varname Name of the member variable that should be mapped to this
	 *                 key. 
	 */
	public void registerVariable(String key,String varname) {
		try {
			Field f = getClass().getDeclaredField(varname);
			m_rep.put(key, new MemberPromise(f));
		} catch (SecurityException e) {
			throw new RuntimeException(e);
		} catch (NoSuchFieldException e) {
			throw new RuntimeException(e);
		}
	}
	/**
	 * Map the result of a member function to a specific key.
	 * @param key     Key used in {{@link #getAnnotationsAsMap()}.
	 * @param funname Name of the member function to call when a mapping for
	 * 				   <code>key</code> is requested. 
	 */
	public void registerFunction(String key,String funname) {
		try {
			Method m = getClass().getDeclaredMethod(funname, (Class[])null);
			m_rep.put(key, new MemfunPromise(m));
		} catch (SecurityException e) {
			throw new RuntimeException(e);
		} catch (NoSuchMethodException e) {
			throw new RuntimeException(e);
		}
	}
	/**
	 * Registers all variables in the top most class in the hierarchy.
	 * The key is the name of the member variable with an optional prefix of
	 * the form <code>?'_'</code> (any letter followed by an underscore)
	 * removed.
	 */
	public void registerAllVariables() {
		Field[] fields = getClass().getDeclaredFields();
		for (Field f : fields) {
			String key = f.getName();
			// Remove coding convention prefix
			if (key.length() > 2 && key.charAt(1) == '_')
				key = key.substring(2);
			m_rep.put(key,new MemberPromise(f));
		}
	}
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return new AbstractMap<String, Object>() {
			private Set<Entry<String, Object>> m_entrySet = 
				new AbstractSet<Entry<String, Object>>() {

				@Override
				public Iterator<Entry<String, Object>> iterator() {
					return new Iterator<Entry<String,Object>>() {
						private Iterator<Entry<String,IPromise>> m_it = 
							m_rep.entrySet().iterator(); 
						@Override
						public boolean hasNext() {
							return m_it.hasNext();
						}

						@Override
						public Entry<String, Object> next() {
							Entry<String, IPromise> n = m_it.next();
							return 
								new AbstractMap.SimpleImmutableEntry<String,Object>(
										n.getKey(),
										n.getValue().evaluate(PromiseAnnotations.this));
						}

						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
						
					};
				}

				@Override
				public int size() {
					// TODO Auto-generated method stub
					return m_rep.size();
				}
				
			};
			@Override
			public Set<java.util.Map.Entry<String, Object>> entrySet() {
				return m_entrySet;
			}
			
		};
	}
}
