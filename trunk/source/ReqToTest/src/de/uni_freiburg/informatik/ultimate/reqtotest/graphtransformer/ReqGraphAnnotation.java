package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

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
	
	private final ReqGuardGraph mReqAut;
	private final TimedLabel mSourceLabel;
	private final ReqGuardGraph mSource;
	
	public ReqGraphAnnotation(ReqGuardGraph reqId, TimedLabel label, ReqGuardGraph source) {
		mReqAut = reqId;
		mSourceLabel = label;
		mSource = source;
	}
	
	public ReqGuardGraph getRequirementAut() {
		return mReqAut;
	}
	
	public ReqGuardGraph getSourceLocation() {
		return mSource;
	}
	
	public Term getGuard() {
		return mSourceLabel.getGuard();
	}
	
	public TimedLabel getLabel() {
		return mSourceLabel;
	}
	
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		HashMap<String, Object> values = new HashMap<String, Object>();
		values.put("reqId: ", mReqAut);
		values.put("label: ", mSourceLabel);
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
		if (other == this) {
			return this;
		} else if (other instanceof ReqGraphAnnotation) {
			//Only use the back translated version where no merging was done.
			return this;
		} else {
			return super.merge(other);
		}
	}


}
