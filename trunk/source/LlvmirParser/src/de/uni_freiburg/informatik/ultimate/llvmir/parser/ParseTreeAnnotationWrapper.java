package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class ParseTreeAnnotationWrapper implements IAnnotations {
	private static final long serialVersionUID = -4852994471225170702L;
	private final Map<String, ParseTree> mMap;
	private final ParseTree mParseTree;
	
	public ParseTreeAnnotationWrapper(final ParseTree parseTree) {
		mMap = new HashMap<>();
		this.mParseTree = parseTree;
		put(parseTree.getClass().getName(), parseTree);
	}

	public ParseTree get(final String key) {
		return mMap.get(key);
	}
	
	public ParseTree getParseTree() {
		return mParseTree;
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return new HashMap<>(mMap);
	}

	public void put(final String key, final ParseTree value) {
		mMap.put(key, value);
	}

	public Set<String> keySet() {
		return mMap.keySet();
	}

	public boolean containsKey(final String key) {
		return mMap.containsKey(key);
	}

	@Override
	public String toString() {
		return mMap.toString();
	}
}
