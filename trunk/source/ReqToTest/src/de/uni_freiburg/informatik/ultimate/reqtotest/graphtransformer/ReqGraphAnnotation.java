package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations.UnmergeableAnnotationsException;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.TimedLabel;

public class ReqGraphAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	
	private final ArrayList<ReqGuardGraph> mSourceLocation;
	private final ArrayList<TimedLabel> mSourceLabel;
	
	public ReqGraphAnnotation(ReqGuardGraph location, TimedLabel label) {
		mSourceLocation = new ArrayList<ReqGuardGraph>();
		mSourceLocation.add(location);
		mSourceLabel = new ArrayList<TimedLabel>();
		mSourceLabel.add(label);
	}
	
	public ArrayList<ReqGuardGraph> getSourceLocation() {
		return mSourceLocation;
	}
	
	public ArrayList<TimedLabel> getSourceLabel() {
		return mSourceLabel;
	}
	
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		HashMap<String, Object> values = new HashMap<String, Object>();
		values.put("location", mSourceLocation);
		values.put("label", mSourceLabel);
		return values;
	}
	
	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(ReqGraphAnnotation.class.getName(), this);
	}

	public static ReqGraphAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, ReqGraphAnnotation.class.getName(), a -> (ReqGraphAnnotation) a);
	}
	
	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof ReqGraphAnnotation) {
			mSourceLocation.addAll(((ReqGraphAnnotation)other).getSourceLocation());
			mSourceLabel.addAll(((ReqGraphAnnotation)other).getSourceLabel());
			return this;
		} else {
			return super.merge(other);
		}
	}


}
