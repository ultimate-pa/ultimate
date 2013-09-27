package PatternLanguage;

import java.util.Vector;

import pea.BooleanDecision;
import pea.CDD;
import pea.PhaseEventAutomata;
import pea.modelchecking.J2UPPAALWriterV4;

/**
 * The class <code>PL_initiated</code> implements the parser, that checks for a given requirement (in string) 
 * whether this requirement matches to a supported pattern (as defined by PL_PatternList).
 * 
 * If a pattern matches, then the function determines the scope, the pattern class and the literals of the
 * instantiated pattern(=requirement). 
 * 
 *
 * @author Amalinda Oertel
 * April 2010
 * 
 * 
 * @see PL_PatternList
 */

public class PL_initiatedPattern {
	
	//das ist die Grammatik auf der wir aufbauen
	private PL_PatternList patternList;
	
	// das sind die geparsten Informationen die wir brauchen
	private String scope;
	private Vector<String> nonLiteralTerminals;
	private PL_Pattern patternClass;
	
	//das sind die Informationen, die wir brauchen, wenn wir die NonLiteralTerminals als CDDs verstehen und 
	//sichergehen wollen, dass zu jeden NonLiteralTerminal GENAU EIN CDD existiert
	private Vector<CDD> nonLiteralTerminalsCDD;
	private Vector<CDD> listOfCDDs;
	
	//nur vorsichtshalber
	private CDD error = BooleanDecision.create("ERROR: Not enough NonLiteralTerminals");
	
	public PL_initiatedPattern(String sentence){
		patternList = new PL_PatternList();
		this.initiatePattern(sentence);
		
	}
	
	public PL_initiatedPattern(String sentence, Vector<CDD> listOfCDDs){
		patternList = new PL_PatternList();
		this.listOfCDDs = listOfCDDs;
		this.initiatePattern(sentence, listOfCDDs);
		
	}
	
	//PL_initiatedPattern
	private void initiatePattern(String sentence){
		//First determine the patternClass
		patternClass = patternList.findMatchingPattern(sentence);
		//if (patternClass.getPatternName() == "init"){
		//	System.out.println("ERROR: PL_initiatePattern: no matching Pattern found");
		//}
		
		//Determine nonLiteralTerminals
		nonLiteralTerminals = patternList.getNonLiteralTerminals(sentence);
		
		//Determine scope
		scope = patternList.getScope(sentence);
		
	}
	
	private String getNonLiteralTerminalNr(int i){
		return nonLiteralTerminals.elementAt(i);
	}
	
	private CDD getCDDFromList(int i){
		return listOfCDDs.elementAt(i);
	}
	
	//PL_initiatedPattern
	private void initiatePattern(String sentence, Vector<CDD> listOfCDDs){
		//First determine the patternClass
		patternClass = patternList.findMatchingPattern(sentence);
		//if (patternClass.getPatternName() == "init"){
		//	System.out.println("ERROR: PL_initiatePattern: no matching Pattern found");
		//}
		
		//Determine nonLiteralTerminals as String
		nonLiteralTerminals = patternList.getNonLiteralTerminals(sentence);
		//Determine nonLiteralTerminals as CDD
		nonLiteralTerminalsCDD = new Vector<CDD>();	
		int cddCount = listOfCDDs.size();
		for (int i=0; i<nonLiteralTerminals.size();i++){
			String nLTerminal = getNonLiteralTerminalNr(i);
			
			
			boolean matchFound = false;
			try
		    {
				Integer.valueOf(nLTerminal).intValue(); //wenn das ein integer ist, dann muß man nix machen
		    }
		    catch(Exception ex)   //not integer value but nonLiteralTerminal String
		    {
		    	for (int j=0; (j<cddCount && !matchFound);j++){
					CDD cdd = getCDDFromList(j);
					cdd.toDNF_CDD();
					if (nLTerminal.matches(cdd.toString())){
							nonLiteralTerminalsCDD.add(cdd);
							matchFound=true;
						}
					if (nLTerminal.matches(cdd.negate().toString())){
							nonLiteralTerminalsCDD.add(cdd.negate());
							matchFound=true;
						}
								
					if (j==(cddCount-1) && !matchFound){
						System.out.println("ERROR in PL_initiatePattern: nonLiteralTerminal "+nLTerminal+" was not found in CDDList"+listOfCDDs.toString());
					}
				
		    }
		    }
		}
		
		//Determine scope
		scope = patternList.getScope(sentence);
		
	}

	//Getter und Setter
	public String getScope() {
		return scope;
	}

	public Vector<String> getNonLiteralTerminals() {
		return nonLiteralTerminals;
	}
	
	public Vector<CDD> getNonLiteralTerminalsCDD() {
		return nonLiteralTerminalsCDD;
	}

	public PL_Pattern getPatternClass() {
		return patternClass;
	}
	
	public String getFirstNonLiteralTerminal(){
		return nonLiteralTerminals.firstElement();
	}
	
	public CDD getFirstNonLiteralTerminalCDD(){
		return nonLiteralTerminalsCDD.firstElement();
	}
	
	public String getSecondNonLiteralTerminal(){
		if (nonLiteralTerminals.size()>1){
			return nonLiteralTerminals.elementAt(1);
		} else
			return "ERROR: Not enough NonLiteralTerminals";		
	}
	
	public CDD getSecondNonLiteralTerminalCDD(){
		if (nonLiteralTerminalsCDD.size()>1){
			return nonLiteralTerminalsCDD.elementAt(1);
		} else
		{
			System.out.println("ERROR: Not enough NonLiteralTerminals");	
			return  error;
		}
	}
	
	public String getThirdNonLiteralTerminal(){
		if (nonLiteralTerminals.size()>2){
			return nonLiteralTerminals.elementAt(2);
		} else
			return "ERROR: Not enough NonLiteralTerminals";		
	}
	
	public CDD getThirdNonLiteralTerminalCDD(){
		if (nonLiteralTerminalsCDD.size()>2){
			return nonLiteralTerminalsCDD.elementAt(2);
		} else
		{
			System.out.println("ERROR: Not enough NonLiteralTerminals");	
			return  error;
		}
	}
	
	public String getFourthNonLiteralTerminal(){
		if (nonLiteralTerminals.size()>3){
			return nonLiteralTerminals.elementAt(3);
		} else
			return "ERROR: Not enough NonLiteralTerminals";		
	}
	
	public CDD getFourthNonLiteralTerminalCDD(){
		if (nonLiteralTerminalsCDD.size()>3){
			return nonLiteralTerminalsCDD.elementAt(3);
		} else
		{
			System.out.println("ERROR: Not enough NonLiteralTerminals");	
			return  error;
		}
	}
	
	public String getFifthNonLiteralTerminal(){
		if (nonLiteralTerminals.size()>4){
			return nonLiteralTerminals.elementAt(4);
		} else
			return "ERROR: Not enough NonLiteralTerminals";		
	}
	
	public CDD getFifthNonLiteralTerminalCDD(){
		if (nonLiteralTerminalsCDD.size()>4){
			return nonLiteralTerminalsCDD.elementAt(4);
		} else
		{
			System.out.println("ERROR: Not enough NonLiteralTerminals");	
			return  error;
		}
	}
	
	public String getSixthNonLiteralTerminal(){
		if (nonLiteralTerminals.size()>5){
			return nonLiteralTerminals.elementAt(5);
		} else
			return "ERROR: Not enough NonLiteralTerminals";		
	}
	
	public CDD getSixthNonLiteralTerminalCDD(){
		if (nonLiteralTerminalsCDD.size()>5){
			return nonLiteralTerminalsCDD.elementAt(5);
		} else
		{
			System.out.println("ERROR: Not enough NonLiteralTerminals");	
			return  error;
		}
	}
	
	public boolean patternRecognized(){
		if (this.patternClass.getPatternName() == "init"){
			return false;
		}
		else return true;
	}
	
	public PhaseEventAutomata transformToPEA(){
		PL_Pattern2Logic toLogic = new PL_Pattern2Logic();
		toLogic.transformPatternToLogic(this, "DC");
		PhaseEventAutomata pea = toLogic.getLogicPEA("DC");

		return pea;
	}
	
public static void main(String[] param) {
		
		CDD p = BooleanDecision.create("P");
		CDD p2 = p.negate();
		String ps = "P";
		System.out.println(ps.matches(p.toString()));
		System.out.println(ps.matches(p2.toString()));
		
	    }

	

}
