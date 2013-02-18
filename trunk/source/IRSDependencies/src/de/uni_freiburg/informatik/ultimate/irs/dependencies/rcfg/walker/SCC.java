package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

public class SCC implements Iterable<RCFGNode> {
	private HashSet<RCFGNode> mVertices;

	public SCC() {
		mVertices = new HashSet<>();
	}

	public <T extends RCFGNode> SCC(Collection<T> all) {
		mVertices = new HashSet<RCFGNode>(all);

	}

	void add(RCFGNode member) {
		mVertices.add(member);
	}

	@Override
	public Iterator<RCFGNode> iterator() {
		return mVertices.iterator();
	}

	public boolean isSingleton() {
		return mVertices.size() == 1;
	}

	public boolean isSingletonOrEmpty() {
		return isSingleton() || isEmpty();
	}

	public boolean isEmpty() {
		return mVertices.isEmpty();
	}

	public boolean contains(RCFGNode node) {
		return mVertices.contains(node);
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		for (RCFGNode node : mVertices) {
			sb.append(node).append(" ");
		}
		if (!isEmpty()) {
			sb.deleteCharAt(sb.length() - 1);
		}
		sb.append(")");
		return sb.toString();
	}

}
