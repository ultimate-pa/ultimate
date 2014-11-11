package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizer;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark the
 * root node so {@link BuchiAutomizer} knows that it should run in LTL mode.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */

public class BuchiProgramRootNodeAnnotation extends Check {

	private static final long serialVersionUID = 1L;
	private static final String sKey = BuchiProgramRootNodeAnnotation.class.getSimpleName();
	private static final String[] sFieldNames = new String[] { "Check", "UseLTLMode", "LTL Property" };

	private final String mLTLProptery;

	public BuchiProgramRootNodeAnnotation(String ltlPropertyAsString) {
		super(Spec.LTL);
		mLTLProptery = ltlPropertyAsString;
	}

	public String getLTLProperty() {
		return mLTLProptery;
	}

	@Override
	public String getNegativeMessage() {
		return "The LTL property " + mLTLProptery + " was violated.";
	}

	@Override
	public String getPositiveMessage() {
		return "The LTL property " + mLTLProptery + " holds.";
	}

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field.equals(sFieldNames[0])) {
			return getSpec().toString();
		} else if (field.equals(sFieldNames[1])) {
			return true;
		} else if (field.equals(sFieldNames[2])) {
			return getLTLProperty();
		} else {
			return null;
		}
	}

	public void annotate(IElement elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static BuchiProgramRootNodeAnnotation getAnnotation(IElement elem) {
		if (!elem.hasPayload()) {
			return null;
		}
		if (!elem.getPayload().hasAnnotation()) {
			return null;
		}
		return (BuchiProgramRootNodeAnnotation) elem.getPayload().getAnnotations().get(sKey);
	}

}
