package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.result.IRelevanceInformation;

public class RelevanceInformation implements IRelevanceInformation 
{

	public CodeBlock statement = null;
	@Override
	public IRelevanceInformation merge(IRelevanceInformation... relevanceInformations) 
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getShortString() 
	{
		// TODO Auto-generated method stub
		return "Returning the string";
	}

	public void setStatement(CodeBlock st) {
		statement = st;
		
	}

}