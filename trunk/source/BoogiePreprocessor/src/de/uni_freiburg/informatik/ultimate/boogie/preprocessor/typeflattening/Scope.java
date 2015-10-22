package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <K>
 * @param <V>
 */
final class Scope<K, V> {

	private final Map<Object, Map<K, V>> mDecls;
	private final Stack<Object> mScope;
	private final static Object GLOBAL = new Object();

	public Scope() {
		mDecls = new HashMap<Object, Map<K, V>>();
		mScope = new Stack<>();
		beginScope(GLOBAL);
	}

	public void beginScope(Object scope) {
		mScope.push(scope);
		getDecls(scope);
	}

	public void endScope(final Object oldScope, final Object newScope) {
		final Object currentScope = mScope.pop();
		assert currentScope != GLOBAL;
		assert currentScope == oldScope;
		assert !mScope.isEmpty();

		if (oldScope != newScope) {
			final Map<K, V> oldScopeDecls = getDecls(oldScope);
			mDecls.remove(oldScope);
			mDecls.put(newScope, oldScopeDecls);
		}
	}

	public void endScope(Object scope) {
		endScope(scope, scope);
	}

	public V declare(K key, V value) {
		if (key == null) {
			throw new IllegalArgumentException("This map does not support null keys");
		}
		return getDecls().put(key, value);
	}

	/**
	 * If key is already declared in any scope, replace the old value associated
	 * with key by value and return the old value. If it is not already
	 * declared, insert the pairing in the current scope.
	 * 
	 * @param key
	 * @param value
	 * @return
	 */
	public V replace(K key, V value) {
		if (key == null) {
			throw new IllegalArgumentException("This map does not support null keys");
		}
		Map<K, V> decls = lookupScope(key);
		if (decls != null) {
			return decls.put(key, value);
		}
		return declare(key, value);
	}

	public V lookup(K key) {
		final Iterator<Object> iter = mScope.iterator();
		while (iter.hasNext()) {
			final Map<K, V> currentDecls = mDecls.get(iter.next());
			final V rtr = currentDecls.get(key);
			if (rtr != null) {
				return rtr;
			}
		}
		return null;
	}
	
	public V lookupCurrentScope(K key) {
		return getDecls().get(key);
	}

	private Map<K, V> lookupScope(K key) {
		final Iterator<Object> iter = mScope.iterator();
		while (iter.hasNext()) {
			final Map<K, V> currentDecls = mDecls.get(iter.next());
			final V rtr = currentDecls.get(key);
			if (rtr != null) {
				return currentDecls;
			}
		}
		return null;
	}

	private Map<K, V> getDecls() {
		return getDecls(mScope.peek());
	}

	private Map<K, V> getDecls(final Object scope) {
		assert scope != null;
		Map<K, V> decls = mDecls.get(scope);
		if (decls == null) {
			decls = new HashMap<K, V>();
			mDecls.put(scope, decls);
		}
		return decls;
	}

	private Map<K, V> flatten() {
		final Map<K, V> flattenedMap = new HashMap<K, V>();
		final Iterator<Object> iter = mScope.iterator();
		while (iter.hasNext()) {
			final Map<K, V> currentDecls = mDecls.get(iter.next());
			for (final Entry<K, V> entry : currentDecls.entrySet()) {
				if(!flattenedMap.containsKey(entry.getKey())){
					flattenedMap.put(entry.getKey(), entry.getValue());
				}
			}
		}
		return flattenedMap;
	}

	@Override
	public String toString() {
		return flatten().toString();
	}
}