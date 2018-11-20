package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.TimedLabel;

public class ReqGraphAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	
	private final ArrayList<ReqGuardGraph> mReqIds;
	private final ArrayList<Term> mSourceLabels;
	
	public ReqGraphAnnotation(ReqGuardGraph reqId, Term label) {
		mReqIds = new ArrayList<ReqGuardGraph>();
		mReqIds.add(reqId);
		mSourceLabels = new ArrayList<Term>();
		mSourceLabels.add(label);
	}
	
	public ArrayList<ReqGuardGraph> getRequirementIds() {
		return mReqIds;
	}
	
	public ArrayList<Term> getGuards() {
		return mSourceLabels;
	}
	
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		HashMap<String, Object> values = new HashMap<String, Object>();
		values.put("reqId: ", mReqIds);
		values.put("label: ", mSourceLabels);
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
			mReqIds.addAll(((ReqGraphAnnotation)other).getRequirementIds());
			mSourceLabels.addAll(((ReqGraphAnnotation)other).getGuards());
			return this;
		} else {
			return super.merge(other);
		}
	}


}
