package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.biesenb;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class TransitiveClosureIG<T extends IPredicate> {

	private Set<ImplicationVertex<T>> mVertices;
	private final Map<ImplicationVertex<T>, Set<ImplicationVertex<T>>> mDescendantsMapping;
	private final Map<ImplicationVertex<T>, Set<ImplicationVertex<T>>> mAncestorsMapping;

	public TransitiveClosureIG(final ImplicationGraph<T> graph) {
		mVertices = new HashSet<>(graph.getVertices());
		mDescendantsMapping = new HashMap<>();
		mAncestorsMapping = new HashMap<>();
		constructTransitiveClosure();
	}

	private void constructTransitiveClosure() {
		mVertices.forEach(v -> mDescendantsMapping.put(v, new HashSet<>(v.getDescendants())));
		mVertices.forEach(v -> mAncestorsMapping.put(v, new HashSet<>(v.getAncestors())));
	}

	public TransitiveClosureIG(final ImplicationGraph<T> graph, final Set<ImplicationVertex<T>> init) {
		mVertices = new HashSet<>(init.iterator().next().getDescendants());
		for (final ImplicationVertex<T> i : init) {
			final Set<ImplicationVertex<T>> current = new HashSet<>();
			for (final ImplicationVertex<T> v : mVertices) {
				if (i.getDescendants().contains(v)) {
					current.add(v);
				}
			}
			mVertices = current;
		}
		mVertices.addAll(init);
		mDescendantsMapping = new HashMap<>();
		mAncestorsMapping = new HashMap<>();
		constructSubTransitiveClosure();
	}

	private void constructSubTransitiveClosure() {
		for (final ImplicationVertex<T> v : mVertices) {
			final Set<ImplicationVertex<T>> descendants = new HashSet<>();
			for (final ImplicationVertex<T> descendant : v.getDescendants()) {
				if (mVertices.contains(descendant)) {
					descendants.add(descendant);
				}
			}
			mDescendantsMapping.put(v, descendants);

			final Set<ImplicationVertex<T>> ancestors = new HashSet<>();
			for (final ImplicationVertex<T> ancestor : v.getAncestors()) {
				if (mVertices.contains(ancestor)) {
					ancestors.add(ancestor);
				}
			}
			mAncestorsMapping.put(v, ancestors);
		}
	}

	/**
	 * fore restructure
	 */
	public TransitiveClosureIG(final ImplicationVertex<T> root, final Set<ImplicationVertex<T>> descendants,
			final ImplicationVertex<T> falseVertex) {
		mVertices = new HashSet<>(descendants);
		mVertices.add(root);
		mDescendantsMapping = new HashMap<>();
		mAncestorsMapping = new HashMap<>();
		for (final ImplicationVertex<T> v : mVertices) {
			final Set<ImplicationVertex<T>> des = new HashSet<>();
			for (final ImplicationVertex<T> descendant : v.getDescendants()) {
				if (mVertices.contains(descendant)) {
					des.add(descendant);
				}
			}
			mDescendantsMapping.put(v, des);
			final Set<ImplicationVertex<T>> ancestors = new HashSet<>();
			for (final ImplicationVertex<T> ancestor : v.getAncestors()) {
				if (mVertices.contains(ancestor)) {
					ancestors.add(ancestor);
				}
			}
			mAncestorsMapping.put(v, ancestors);
		}
		mVertices.add(falseVertex);
		mAncestorsMapping.put(falseVertex, new HashSet<>());
		mDescendantsMapping.put(falseVertex, new HashSet<>());
		for (final ImplicationVertex<T> ancestor : mAncestorsMapping.keySet()) {
			if (mAncestorsMapping.get(ancestor).isEmpty()) {
				mAncestorsMapping.get(ancestor).add(falseVertex);
				mDescendantsMapping.get(falseVertex).add(ancestor);
			}
		}
	}

	protected void removeVertex(final ImplicationVertex<T> vertex) {
		if (mVertices.remove(vertex)) {
			final Set<ImplicationVertex<T>> descendants = mDescendantsMapping.remove(vertex);
			descendants.forEach(d -> mAncestorsMapping.get(d).remove(vertex));
			final Set<ImplicationVertex<T>> ancestors = mAncestorsMapping.remove(vertex);
			ancestors.forEach(a -> mDescendantsMapping.get(a).remove(vertex));
		}
	}

	public void removeAncestorsFromTC(final ImplicationVertex<T> vertex) {
		while (!mAncestorsMapping.get(vertex).isEmpty()) {
			final ImplicationVertex<T> remove = mAncestorsMapping.get(vertex).iterator().next();
			if (mVertices.remove(remove)) {
				final Set<ImplicationVertex<T>> descendants = mDescendantsMapping.remove(remove);
				descendants.forEach(d -> mAncestorsMapping.get(d).remove(remove));
				final Set<ImplicationVertex<T>> ancestors = mAncestorsMapping.remove(remove);
				ancestors.forEach(a -> mDescendantsMapping.get(a).remove(remove));
			}
		}
	}

	/**
	 * If null is given as trueVertex it will be removed, else it remains
	 */
	public void removeDescendantsFromTC(ImplicationVertex<T> vertex, final ImplicationVertex<T> trueVertex) {
		if (trueVertex == null) {
			while (!mDescendantsMapping.get(vertex).isEmpty()) {
				removeVertex(mDescendantsMapping.get(vertex).iterator().next());
			}
		} else {
			final Set<ImplicationVertex<T>> a = new HashSet<>(mDescendantsMapping.get(vertex));
			while (!a.isEmpty()) {
				vertex = a.iterator().next();
				a.remove(vertex);
				if (!vertex.equals(trueVertex)) {
					removeVertex(vertex);
				} else {
					mAncestorsMapping.get(trueVertex).clear();
				}
			}
			for (final ImplicationVertex<T> d : mDescendantsMapping.keySet()) {
				if (mDescendantsMapping.get(d).isEmpty()) {
					mDescendantsMapping.get(d).add(trueVertex);
					mAncestorsMapping.get(trueVertex).add(d);
				}
			}
		}
	}

	/**
	 * @param marked
	 *            - these vertices can't be chosen
	 * @param first
	 *            - if true one is added to a, else to b
	 * @returns the vertex with the highest count which is calculated from the number of ancestors and descendants
	 */
	protected ImplicationVertex<T> getMaxTransitiveClosureCount(final Set<ImplicationVertex<T>> marked,
			final boolean first) {
		int max = 0;
		ImplicationVertex<T> maxVertex = mVertices.iterator().next();
		for (final ImplicationVertex<T> vertex : mVertices) {
			if (marked.contains(vertex)) {
				continue;
			}
			int a = mAncestorsMapping.get(vertex).size();
			int b = mDescendantsMapping.get(vertex).size();
			if (first) {
				b += 1;
			} else {
				a += 1;
			}
			final int count = (a * b) / (a + b);
			if (count >= max) {
				max = count;
				maxVertex = vertex;
			}
		}
		// ImplicationVertex<T> maxVertex = mVertices.iterator().next();
		// for (final ImplicationVertex<T> vertex : mVertices) {
		// if (!marked.contains(vertex)) {
		// return vertex;
		// }
		// }
		return maxVertex;
	}

	protected Map<ImplicationVertex<T>, Set<ImplicationVertex<T>>> getDescendantsMapping() {
		return mDescendantsMapping;
	}

	protected Map<ImplicationVertex<T>, Set<ImplicationVertex<T>>> getAncestorsMapping() {
		return mAncestorsMapping;
	}

	protected Set<ImplicationVertex<T>> getVertices() {
		return mVertices;
	}
}
