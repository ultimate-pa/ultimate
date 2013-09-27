package req_to_pea;


import pea.modelchecking.J2UPPAALConverter;
import pea.reqCheck.PatternToPEA;

import org.antlr.runtime.*;


import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pea.*;

import srParse.*;

public class ReqToPEA {
    public Vector<srParsePattern> genPatterns(String reqFileName) throws ENotDeclaredIdentifier {
    	Vector<srParsePattern> patterns = null;
    	try{
		        CharStream cs = new ANTLRFileStream(reqFileName);
		
		        SRboolLexer l=new SRboolLexer(cs);
		
		        TokenStream tokens = new CommonTokenStream(l);		
		        SRboolParser p=new SRboolParser(tokens);
		    try{
			    p.file();			
			    srParseController contr=srParseController.getInstance();
			    patterns=contr.getPatterns();
		    }
		    catch(Exception e)
		    {
			    e.printStackTrace();
		    }
		}
		catch(Exception e)
		{
		    e.printStackTrace();
		}
		return patterns;
}
	public PhaseEventAutomata[] genPEA(Vector<srParsePattern> patterns){
		List<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>();

		try{		
			int i;
			PhaseEventAutomata pea=null;				
			
			PatternToPEA peaTrans=new PatternToPEA();
			
			for(i=0;i<patterns.size();i++ )
			{
				patterns.get(i).setPeaTransformator( peaTrans );
				if( pea==null )
				{
					pea=patterns.get(i).transformToPea();
					peaList.add(pea);
				}
				else
				{	
					PhaseEventAutomata pea2=patterns.get(i).transformToPea();
					
					if( pea2==null )
						continue;					
					//pea=pea.parallel( pea2 );
				peaList.add(pea2);
					
				}								
			}
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}

		
		PhaseEventAutomata[] peaArray = peaList.toArray(new PhaseEventAutomata[peaList.size()]);
	    return peaArray;	
	}
	public void genPEAforUPPAAL(Vector<srParsePattern> patterns, String xmlFilePath) {

		try{
			int i;
			PhaseEventAutomata pea=null;				
			
			PatternToPEA peaTrans=new PatternToPEA();
			
			for(i=0;i<patterns.size();i++ )
			{
				patterns.get(i).setPeaTransformator( peaTrans );
				if( pea==null )
				{
					pea=patterns.get(i).transformToPea();

				}
				else
				{	
					PhaseEventAutomata pea2=patterns.get(i).transformToPea();
					
					if( pea2==null )
						continue;					
					pea=pea.parallel( pea2 );
				
				}								
			}			
			J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
			uppaalConverter.writePEA2UppaalFile(xmlFilePath, pea);									
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}	
	}
}


