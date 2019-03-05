package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.TimedLabel;

public class ReqGraphOracleAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	
	private final ReqGuardGraph mReqAut;
	private final Term mOracle;
	private final Collection<TermVariable> mOracleVars;
	
	public ReqGraphOracleAnnotation(ReqGuardGraph reqId, Term oracle, Collection<TermVariable> oracleVars) {
		mReqAut = reqId;
		mOracle = oracle;
		mOracleVars = oracleVars;
	}
	
	public ReqGuardGraph getRequirementAut() {
		return mReqAut;
	}
	
	public Term getOracle() {
		return mOracle;
	}
	
	public Collection<TermVariable> getOracleVars() {
		//TODO: filter for constants
		return mOracleVars;
	}
	
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		HashMap<String, Object> values = new HashMap<String, Object>();
		values.put("reqId: ", mReqAut);
		values.put("oracle: ", mOracle);
		return values;
	}
	
	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(ReqGraphOracleAnnotation.class.getName(), this);
	}

	public static ReqGraphOracleAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, ReqGraphOracleAnnotation.class.getName(), a -> (ReqGraphOracleAnnotation) a);
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
