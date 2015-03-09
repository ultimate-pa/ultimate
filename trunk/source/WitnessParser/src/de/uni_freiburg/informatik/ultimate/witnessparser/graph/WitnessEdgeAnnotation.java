package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

public class WitnessEdgeAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = Activator.s_PLUGIN_ID + "_Edge";
	private static final String[] sFieldNames = new String[] { "Condition", "EnterFrom", "ReturnFrom", "Tokens",
			"Assumption" };

	private final Boolean mCondition;
	private final String mEnterFrom;
	private final String mReturnFrom;
	private final String mTokens;
	private final String mAssumption;

	public WitnessEdgeAnnotation(String condition, String enterFrom, String returnFrom, String tokens, String assumption) {
		this(condition != null ? Boolean.valueOf(condition) : null, enterFrom, returnFrom, tokens, assumption);
	}

	public WitnessEdgeAnnotation(Boolean condition, String enterFrom, String returnFrom, String tokens,
			String assumption) {
		mCondition = condition;
		mEnterFrom = enterFrom;
		mReturnFrom = returnFrom;
		mTokens = tokens;
		mAssumption = assumption;
	}

	public Boolean getCondition() {
		return mCondition;
	}

	public String getEnterFrom() {
		return mEnterFrom;
	}

	public String getReturnFrom() {
		return mReturnFrom;
	}

	public String getTokens() {
		return mTokens;
	}

	public String getAssumption() {
		return mAssumption;
	}

	public boolean isEmpty() {
		return getCondition() == null && getEnterFrom() == null && getReturnFrom() == null && getTokens() == null
				&& getAssumption() == null;
	}

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "Condition":
			return mCondition;
		case "EnterFrom":
			return mEnterFrom;
		case "ReturnFrom":
			return mReturnFrom;
		case "Tokens":
			return mTokens;
		case "Assumption":
			return mAssumption;
		}
		return null;
	}

	public void annotate(IElement elem) {
		if (elem instanceof WitnessEdge) {
			annotate((WitnessEdge) elem);
		}
	}

	public void annotate(WitnessEdge elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static WitnessEdgeAnnotation getAnnotation(IElement elem) {
		if (elem instanceof WitnessEdge) {
			getAnnotation((WitnessEdge) elem);
		}
		return null;
	}

	public static WitnessEdgeAnnotation getAnnotation(WitnessEdge elem) {
		if (elem.hasPayload()) {
			IPayload payload = elem.getPayload();
			if (payload.hasAnnotation()) {
				IAnnotations annot = payload.getAnnotations().get(sKey);
				if (annot != null) {
					return (WitnessEdgeAnnotation) annot;
				}
			}
		}
		return null;
	}
}
