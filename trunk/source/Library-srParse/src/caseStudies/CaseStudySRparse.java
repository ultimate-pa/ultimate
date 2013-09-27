package caseStudies;

import pea.*;
import srParse.*;
import java.util.Vector;

public class CaseStudySRparse {
	
	private Vector<CDD> cdds;

	public Vector<CDD> getCdds() {
		return cdds;
	}

	public void setCdds(Vector<CDD> cdds) {
		this.cdds = cdds;
	}
	
	public Vector<String> getReqs(String filename)
	{
		Vector<String> req;
		ParseL2 parser=new ParseL2();
		
		parser.parse(filename);
		req=parser.getReqs();
		cdds=parser.getVariables();
		
		
		
		return req;
	}

}
