package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;

public class AberranceInformation implements IRelevanceInformation {

	private final TraceAberrance traceAberrant;
	private String mPrettyPrintedStatements;
	
	public AberranceInformation(TraceAberrance traceAberrant) {
		super();
		this.traceAberrant = traceAberrant;
		this.mPrettyPrintedStatements = traceAberrant.toString();
	}
	public TraceAberrance GetTraceAberrance() {
		return traceAberrant;
	}
	@Override
	public IRelevanceInformation merge(IRelevanceInformation... relevanceInformations) {
		// TODO Auto-generated method stub
		return this;
	}

	@Override
	public String getShortString() {
		// TODO Auto-generated method stub
		return this.traceAberrant.toString();
	}
	
	public String toString() {
		return this.traceAberrant.toString();
	}

}


