package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.result.IRelevanceInformation;
import java.util.regex.Pattern;

public class RelevanceInformation implements IRelevanceInformation 
{

	private CodeBlock statement;
	private Boolean criteria1 = false;
	private Boolean criteria2 = false;
	@Override
	public IRelevanceInformation merge(IRelevanceInformation... relevanceInformations) 
	{
		IRelevanceInformation merged_relevency = new RelevanceInformation();
		for(int i=0;i<relevanceInformations.length;i++)
		{
			
			if(relevanceInformations[i].getShortString().indexOf("*") >=0)
			{
				((RelevanceInformation) merged_relevency).setCriteria1(true);
			}
			if(relevanceInformations[i].getShortString().indexOf("#") >= 0)
			{
				((RelevanceInformation) merged_relevency).setCriteria2(true);
			}
			
		}
		return merged_relevency;
	}

	@Override
	public String getShortString() 
	{
		String criteria_string="";
		if(criteria1){
			criteria_string = criteria_string + "*";
		}
		if(criteria2){
			criteria_string = criteria_string + "#";
		}
		return criteria_string;
	}

	public void setStatement(CodeBlock st) {
		statement = st;
		
	}
	
	public CodeBlock getStatement(){
		return statement;
	}


	public void setCriteria1(Boolean criteria1) {
		this.criteria1 = criteria1;
	}
	
	public void setCriteria2(Boolean criteria2) {
		this.criteria2 = criteria2;
	}

}
