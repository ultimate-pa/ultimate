package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

public class WitnessNodeAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = Activator.s_PLUGIN_ID + "_Node";
	private static final String[] sFieldNames = new String[] { "IsInitial", "IsError", "IsSink" };

	private boolean mIsInitial;
	private boolean mIsError;
	private boolean mIsSink;

	public WitnessNodeAnnotation(boolean isInitial, boolean isError, boolean isSink) {
		mIsInitial = isInitial;
		mIsError = isError;
		mIsSink = isSink;
	}

	public boolean isInitial() {
		return mIsInitial;
	}

	public void setIsInitial(boolean isInitial) {
		mIsInitial = isInitial;
	}

	public boolean isError() {
		return mIsError;
	}

	public void setIsError(boolean isError) {
		mIsError = isError;
	}
	
	public boolean isSink() {
		return mIsSink;
	}

	public void setIsSink(boolean isSink) {
		mIsSink = isSink;
	}

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "IsInitial":
			return mIsInitial;
		case "IsError":
			return mIsError;
		case "IsSink":
			return mIsSink;
		}
		return null;
	}

	public void annotate(IElement node) {
		if (node instanceof WitnessNode) {
			annotate((WitnessNode) node);
		}
	}

	public void annotate(WitnessNode node) {
		node.getPayload().getAnnotations().put(sKey, this);
	}

	public static WitnessNodeAnnotation getAnnotation(IElement node) {
		if (node instanceof WitnessNode) {
			getAnnotation((WitnessNode) node);
		}
		return null;
	}

	public static WitnessNodeAnnotation getAnnotation(WitnessNode node) {
		if (node.hasPayload()) {
			IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				IAnnotations annot = payload.getAnnotations().get(sKey);
				if (annot != null) {
					return (WitnessNodeAnnotation) annot;
				}
			}
		}
		return null;
	}
}
