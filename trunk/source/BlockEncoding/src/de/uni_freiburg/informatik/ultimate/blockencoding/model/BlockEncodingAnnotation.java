package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;

public class BlockEncodingAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	private MinimizedNode mNode;

	public BlockEncodingAnnotation(MinimizedNode node) {
		mNode = node;
	}

	public MinimizedNode getNode() {
		return mNode;
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] {};
	}

	@Override
	protected Object getFieldValue(String field) {
		return null;
	}

	public static void addAnnotation(IElement elem, IAnnotations annot) {
		elem.getPayload().getAnnotations().put(Activator.s_PLUGIN_ID, annot);
	}

	public static BlockEncodingAnnotation getAnnotation(IElement elem) {
		if (elem.hasPayload()) {
			IAnnotations rtr = elem.getPayload().getAnnotations()
					.get(Activator.s_PLUGIN_ID);
			if (rtr != null) {
				return (BlockEncodingAnnotation) rtr;
			}
		}
		return null;
	}
}
