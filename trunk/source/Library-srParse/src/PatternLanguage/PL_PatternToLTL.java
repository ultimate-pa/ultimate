package PatternLanguage;

import java.util.Vector;

import pea.BooleanDecision;
import pea.CDD;
import pea.PEANet;
import pea.PhaseEventAutomata;
import pea.reqCheck.PatternToPEA;

/**
 * The class <code>PL_PatternToLTL</code> offers functionality to
 * convert requirements, that are formalized in Patterns provided by <code>PL_PatternList</code>, to their formalization in either
 * Linear Timed Logic "LTL"
 * Computational Tree Logic "CTL"
 * Timed Computational Tree Logic "TCTL"
 * 
 * This code should be only used if you do not need the transformation to DurationCalculus Formulas, and thus do not want to use the
 * PEA package with PhaseEventAutomata. Otherwise use <code>PL_Pattern2Logic</code>
 * 
 * Precondition: a string with a requirement that shall be transformed, was formerly transformed into an "initiatedPattern", thus, 
 * a parser already checked for scope, pattern class and literals
 * 
 *
 * @author Amalinda Oertel
 * April 2010
 * 
 * @see PL_PatternList
 * @see PL_initiatedPattern
 */

public class PL_PatternToLTL {
	///In dieser Klasse werden die Patterns, die in PL_PatternList.java definiert sind, nach LTL, CTL und TCTL übersetzt
	//(je nachdem was möglich ist)
	// Da für jedes Pattern je nach Scope unterschiedlich transformiert werden muß, schaut die Klasse ziemlich scheußlich aus :(
	
	//Die Übersetzten Patterns in NuSMV Syntax werden in der Klasse ToNuSMV generiert;
	
	//Precondition: ein zu übersetzender String wurde zuvor in ein "initiatedPattern" umgewandelt, sprich
	// der String wurde nach Scope, Pattern und den nonLiteralTerminals aufgegliedert
	
	String formulaInLTL;
	String formulaInCTL;
	String formulaInTCTL;
	PEANet formulaInDC;
	
	
	//Constructors
	public PL_PatternToLTL(){
		this.formulaInLTL = "init";
		this.formulaInCTL = "init";
		this.formulaInTCTL = "init";
		this.formulaInDC = new PEANet();
	}

	//Getter/Setter
	public String getFormulaInCTL() {
		return formulaInCTL;
	}

	public void setFormulaInCTL(String formulaInCTL) {
		this.formulaInCTL = formulaInCTL;
	}

	public String getFormulaInTCTL() {
		return formulaInTCTL;
	}

	public void setFormulaInTCTL(String formulaInTCTL) {
		this.formulaInTCTL = formulaInTCTL;
	}
	
	public PEANet getFormulaInDC() {
		return formulaInDC;
	}

	public void setFormulaInDC(PEANet peanet) {
		this.formulaInDC = peanet;
	}
	
	private void addFormulaInDC(PhaseEventAutomata pea) {
		this.formulaInDC.addPEA(pea);
	}
	

	
	public String getFormulaInLTL() {
		return formulaInLTL;
	}

	private void setFormulaInLTL(String formulaInLTL) {
		this.formulaInLTL = formulaInLTL;
	}
	
	//Functions
	public String transformPatternToLTL(PL_initiatedPattern req){
		
		PL_Pattern patternClass = req.getPatternClass();
		PL_PatternList patternList = new PL_PatternList();
		
		if (patternClass.getPatternName() == patternList.getAbsentPattern().getPatternName()){
			return this.transformAbsentPattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getUniversalityPattern().getPatternName()){
			return this.transformUniversalityPattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getExistencePattern().getPatternName()){
			return this.transformExistencePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getPrecedencePattern().getPatternName()){
			return this.transformPrecedencePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getResponsePattern().getPatternName()){
			return this.transformResponsePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getInvariancePattern().getPatternName()){
			return this.transformInvariantPattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getBndExistencePattern().getPatternName()){
			return this.transformbndExistencePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getPrecedenceChainPattern21().getPatternName()){
			return this.transformPrecedenceChain21Pattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getPrecedenceChainPattern12().getPatternName()){
			return this.transformPrecedenceChain12Pattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getConstrainedChainPattern12().getPatternName()){
			return this.transformConstrainedChainPattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getResponseChainPattern21().getPatternName()){
			return this.transformResponseChain21Pattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getResponseChainPattern12().getPatternName()){
			return this.transformResponseChain12Pattern(req);
		}		
		else if (patternClass.getPatternName() == patternList.getPossibilityPattern().getPatternName()){
			return this.transformPossibleResponsePattern(req);
		}
		//Start quantitative patterns
		else if (patternClass.getPatternName() == patternList.getPossBndResponsePattern().getPatternName()){
			return this.transformPossBndResponsePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getPossBndInvariancePattern().getPatternName()){
			return this.transformPossBndInvariancePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getBoundedInvariancePattern().getPatternName()){
			return this.transformBndInvariancePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getBoundedResponsePattern().getPatternName()){
			return this.transformBndResponsePattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getBoundedRecurrencePattern().getPatternName()){
			return this.transformBndReccurrPattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getMinDurationPattern().getPatternName()){
			return this.transformMinDurPattern(req);
		}
		else if (patternClass.getPatternName() == patternList.getMaxDurationPattern().getPatternName()){
			return this.transformMaxDurPattern(req);
		}
		
		else return "ERROR: Unknown pattern --> cannot be transformed to LTL";
	}
	
	
	//Zunächst pro Pattern
		
	protected String transformAbsentPattern(PL_initiatedPattern req){
		
		String scope = req.getScope();
		Vector<String> nonLiteralTerminals = req.getNonLiteralTerminals();
		
		//PL_Pattern patternClass = req.getPatternClass();		
		//hier kein Check ob das auch das richtige Pattern ist, sondern implizite Annahme, dass
		// das früher gecheckt wird
		
		//Case: GLOBALLY
		if (scope.contains("Globally")){
			if (nonLiteralTerminals.size() !=1){
				//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			String p = nonLiteralTerminals.firstElement();
			CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = BooleanDecision.create("Q");
			CDD r_cdd = BooleanDecision.create("R");
			
			this.setFormulaInLTL("G(!("+p.toString()+"))");
			this.setFormulaInCTL("AG(!("+p+"))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			
			PhaseEventAutomata pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			return this.getFormulaInLTL();
		}
		//CASE: BEFORE R
		else 
			if (scope.contains("Before")){
			if (nonLiteralTerminals.size() !=2){
				//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = BooleanDecision.create("Q");
			CDD r_cdd = BooleanDecision.create(r);
			
			this.setFormulaInLTL("F("+r+")->((!("+p+")U "+r+"))");	
			this.setFormulaInCTL("!E(!(("+r+")) U (!((!("+p+") | AG(!("+r+") ))) & !(("+r+"))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			
			PhaseEventAutomata pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			return this.getFormulaInLTL();
		}
		//CASE: AFTER Q UNTIL R
			else 
				if (scope.contains("until")){
				if (nonLiteralTerminals.size() !=3){
					//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
					System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
				}
				String q = req.getFirstNonLiteralTerminal();
				String r = req.getSecondNonLiteralTerminal();
				String p = req.getThirdNonLiteralTerminal();
				
				//p W q = (G p) | (p U q)
				this.setFormulaInLTL("G(("+q+" & !("+r+"))->((G!("+p+")) | (!("+p+") U ("+r+"))))");	
				this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!(!("+p+")) & !(("+r+"))))))");			
				this.setFormulaInTCTL(this.getFormulaInCTL());
				return this.getFormulaInLTL();
			}
		//CASE: AFTER Q
				else 
					if (scope.contains("After")){
					if (nonLiteralTerminals.size() !=2){
						//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
						System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
					}
					String q = req.getFirstNonLiteralTerminal();
					String p = req.getSecondNonLiteralTerminal();
					
					this.setFormulaInLTL("G("+q+" -> G((!("+p+"))))");
					this.setFormulaInCTL("AG(("+q+")->AG(!("+p+") ))");			
					this.setFormulaInTCTL(this.getFormulaInCTL());
					return this.getFormulaInLTL();
				}
		//CASE: BETWEEN Q AND R
					else 
						if (scope.contains("Between")){
						if (nonLiteralTerminals.size() !=3){
							//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
							System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
						}
						String q = req.getFirstNonLiteralTerminal();
						String r = req.getSecondNonLiteralTerminal();
						String p = req.getThirdNonLiteralTerminal();
						
						this.setFormulaInLTL("G(("+q+" & !("+r+") & F("+r+"))->((!("+p+")U "+r+")))");
						this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!((!("+p+") | AG(!("+r+") ))) & !(("+r+"))))))");			
						this.setFormulaInTCTL(this.getFormulaInCTL());
						return this.getFormulaInLTL();
					}
		else return ("cannot be transformed to AbsentPattern");
		
	}
	
protected String transformAbsentPattern(PL_initiatedPattern req, String wantedLogic){
		
		String scope = req.getScope();
		Vector<String> nonLiteralTerminals = req.getNonLiteralTerminals();
		
		PhaseEventAutomata pea;//für DC
		
		//PL_Pattern patternClass = req.getPatternClass();		
		//hier kein Check ob das auch das richtige Pattern ist, sondern implizite Annahme, dass
		// das früher gecheckt wird
		
		
		
		//Case: GLOBALLY
		if (scope.contains("Globally")){
			if (nonLiteralTerminals.size() !=1){
				//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			String p = nonLiteralTerminals.firstElement();
			CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = BooleanDecision.create("Q");
			CDD r_cdd = BooleanDecision.create("R");
			
			this.setFormulaInLTL("G(!("+p+"))");
			this.setFormulaInCTL("AG(!("+p+"))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			
			pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
		}
		//CASE: BEFORE R
		else 
			if (scope.contains("Before")){
			if (nonLiteralTerminals.size() !=2){
				//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = BooleanDecision.create("Q");
			CDD r_cdd = BooleanDecision.create(r);
			
			this.setFormulaInLTL("F("+r+")->((!("+p+")U "+r+"))");	
			this.setFormulaInCTL("!E(!(("+r+")) U (!((!("+p+") | AG(!("+r+") ))) & !(("+r+"))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			
			pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
			
		}
		//CASE: AFTER Q UNTIL R
			else 
				if (scope.contains("until")){
				if (nonLiteralTerminals.size() !=3){
					//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
					System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
				}
				String q = req.getFirstNonLiteralTerminal();
				String r = req.getSecondNonLiteralTerminal();
				String p = req.getThirdNonLiteralTerminal();
				CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
				CDD q_cdd = BooleanDecision.create(q);
				CDD r_cdd = BooleanDecision.create(r);
				
				//p W q = (G p) | (p U q)
				this.setFormulaInLTL("G(("+q+" & !("+r+"))->((G!("+p+")) | (!("+p+") U ("+r+"))))");	
				this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!(!("+p+")) & !(("+r+"))))))");			
				this.setFormulaInTCTL(this.getFormulaInCTL());
				pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
				
			}
		//CASE: AFTER Q
				else 
					if (scope.contains("After")){
					if (nonLiteralTerminals.size() !=2){
						//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
						System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
					}
					String q = req.getFirstNonLiteralTerminal();
					String p = req.getSecondNonLiteralTerminal();
					CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
					CDD q_cdd = BooleanDecision.create(q);
					CDD r_cdd = BooleanDecision.create("R");
					
					this.setFormulaInLTL("G("+q+" -> G((!("+p+"))))");
					this.setFormulaInCTL("AG(("+q+")->AG(!("+p+") ))");			
					this.setFormulaInTCTL(this.getFormulaInCTL());
					pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
				}
		//CASE: BETWEEN Q AND R
					else 
						if (scope.contains("Between")){
						if (nonLiteralTerminals.size() !=3){
							//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
							System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
						}
						String q = req.getFirstNonLiteralTerminal();
						String r = req.getSecondNonLiteralTerminal();
						String p = req.getThirdNonLiteralTerminal();
						CDD p_cdd = BooleanDecision.create(p); //für Duration Calculus muß das als CDD gegeben sein
						CDD q_cdd = BooleanDecision.create(q);
						CDD r_cdd = BooleanDecision.create(r);
						
						this.setFormulaInLTL("G(("+q+" & !("+r+") & F("+r+"))->((!("+p+")U "+r+")))");
						this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!((!("+p+") | AG(!("+r+") ))) & !(("+r+"))))))");			
						this.setFormulaInTCTL(this.getFormulaInCTL());
						pea = new PatternToPEA().absencePattern(p_cdd, q_cdd, r_cdd, scope);
						//return this.getFormulaInLTL();
					}
		else return ("cannot be transformed to AbsentPattern");
		
		if (wantedLogic.contains("LTL")){
			return this.getFormulaInLTL();
		}
		if (wantedLogic.contains("TCTL")){
				return this.getFormulaInTCTL();
		}
		else if (wantedLogic.contains("CTL")){
				return this.getFormulaInCTL();
		}
		if (wantedLogic.contains("DC")){
			return "Pea already dumped";
		}
		else 
			return "requested Logic unkown";
		
	}
	
	//UNIVERSALITY PATTERN
	protected String transformUniversalityPattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformUnivPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformUnivPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformUnivPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformUnivPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformUnivPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to UniversalityPattern";
	}
	//Scope "Globally"
	private String transformUnivPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und universalityPattern
		String p = req.getFirstNonLiteralTerminal();
		this.setFormulaInLTL("G("+p+")");
		this.setFormulaInCTL("AG(("+p+"))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformUnivPat_Before(PL_initiatedPattern req){
		//bei GloballyScope und universalityPattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		
		p= this.toSMVString(p);
		
		r= this.toSMVString(r);
		
		
		
		this.setFormulaInLTL("F("+r+")-> ("+p+" U "+r+")");
		this.setFormulaInCTL("!E(!(("+r+")) U (!((("+p+") |AG(!("+r+") ))) & !(("+r+"))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformUnivPat_After(PL_initiatedPattern req){
		//bei GloballyScope und universalityPattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		
		p= this.toSMVString(p);
		q= this.toSMVString(q);
		
		
		this.setFormulaInLTL("G(("+q+") -> G("+p+"))");
		this.setFormulaInCTL("AG(("+q+") -> AG(("+p+") ))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformUnivPat_Between(PL_initiatedPattern req){
		//bei GloballyScope und universalityPattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		p= this.toSMVString(p);
		r= this.toSMVString(r);
		q= this.toSMVString(q);
		
		
		this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+")) -> (("+p+") U ("+r+")))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!((("+p+") |AG(!("+r+") ))) & !(("+r+"))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformUnivPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		p= this.toSMVString(p);
		r= this.toSMVString(r);
		q= this.toSMVString(q);		
		
		this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (G("+p+") | (("+p+") U ("+r+"))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!("+r+") U (!("+p+") & !("+r+")))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//EXISTENCE PATTERN
	protected String transformExistencePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformExisPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformExisPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformExisPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformExisPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformExisPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ExistencePattern";
	}
	//Scope "Globally"
	private String transformExisPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und existencePattern
		String p = req.getFirstNonLiteralTerminal();
		this.setFormulaInLTL("F("+p+")");
		this.setFormulaInCTL("AF(("+p+") )");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformExisPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und existencePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		
		this.setFormulaInLTL("G(!("+r+"))|(!("+r+") U ("+p+" & (!("+r+"))))");
		this.setFormulaInCTL("!E(!((("+p+") &!("+r+") )) U (!(!("+r+")) & !((("+p+") &!("+r+") ))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformExisPat_After(PL_initiatedPattern req){
		//bei AfterQScope und existencePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		
		this.setFormulaInLTL("G(!("+q+") | F("+q+" & F("+p+")))");
		this.setFormulaInCTL("!E(!((("+q+") & AF(("+p+") ))) U (!(!("+q+")) & !((("+q+") & AF(("+p+") )))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformExisPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und existencePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (G(!("+r+"))|(!("+r+") U ("+p+" & (!("+r+"))))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") ) ->(!E(!((("+p+") &!("+r+") )) U (!(!("+r+")) & !((("+p+") &!("+r+") ))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformExisPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (!("+r+") U ("+p+" & (!("+r+")))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") ) -> A(!("+r+") U (("+p+") &!("+r+") )))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	
	//*********************************************************************************************
	//PRECEDENCE PATTERN
	protected String transformPrecedencePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformPrecPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformPrecPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformPrecPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformPrecPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformPrecPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to PrecedencePattern";
	}
	//Scope "Globally"
	private String transformPrecPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und precedencePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		this.setFormulaInLTL("((G !("+p+"))|(!("+p+") U ("+s+")))");
		this.setFormulaInCTL("!E(!(("+s+")) U (!(!("+p+")) & !(("+s+"))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformPrecPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und precedencePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> (!("+p+") U (("+s+") | ("+r+")))");
		this.setFormulaInCTL("!E(!((("+s+") | ("+r+") )) U (!((!("+p+") |AG(!("+r+") ))) & !((("+s+") | ("+r+") ))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformPrecPat_After(PL_initiatedPattern req){
		//bei AfterQScope und precedencePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G(!("+q+")) | F("+q+" & ((G !("+p+"))|(!("+p+") U ("+s+"))))");
		this.setFormulaInCTL("!E(!((("+q+") & !E(!(("+s+")) U (!(!("+p+")) & !(("+s+")))))) U (!(!("+q+") ) & !((("+q+") & !E(!(("+s+")) U (!(!("+p+")) & !(("+s+"))))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformPrecPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und precedencePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+")) -> (!("+p+") U (("+s+") | ("+r+"))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!((("+s+") |("+r+") )) U (!((!("+p+") | AG(!("+r+") ))) & !((("+s+") |("+r+") ))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformPrecPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & !("+r+")) -> ((G !("+p+"))|(!("+p+") U (("+s+") | ("+r+")))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!((("+s+") |("+r+") )) U (!(!("+p+")) & !((("+s+") |("+r+") ))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//RESPONSE PATTERN
	protected String transformResponsePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformRespPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformRespPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformRespPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformRespPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformRespPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponsePattern";
	}
	//Scope "Globally"
	private String transformRespPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		this.setFormulaInLTL("G(("+p+") -> F("+s+"))");
		this.setFormulaInCTL("AG(("+p+")-> AF(("+s+") ))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformRespPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> (("+p+") -> (!("+r+") U (("+s+") & (!("+r+")))))U("+r+")");
		this.setFormulaInCTL("!E(!(("+r+")) U (!(((("+p+") -> A(!("+r+") U (("+s+") &!("+r+") )))| AG(!("+r+") ))) & !(("+r+"))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformRespPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> F("+s+")))");
		this.setFormulaInCTL("!E(!((("+q+") &AG(("+p+")->AF(("+s+") )))) U (!(!("+q+") ) & !((("+q+") &AG(("+p+")->AF(("+s+") ))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformRespPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+")) -> (("+p+") -> (!("+r+") U (("+s+") & (!("+r+"))))) U ("+r+"))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!(((("+p+")->A(!("+r+") U (("+s+") &!("+r+") ))) | AG(!("+r+") ))) & !(("+r+"))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformRespPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (G(("+p+") -> (!("+r+") U (("+s+") & (!("+r+"))))) | ((("+p+") -> (!("+r+") U (("+s+") & (!("+r+"))))) U("+r+"))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!((("+p+")->A(!("+r+") U (("+s+") &!("+r+") )))) & !(("+r+"))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//Invariant PATTERN
	protected String transformInvariantPattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformInvPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformInvPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformInvPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformInvPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformInvPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to InvariantPattern";
	}
	//Scope "Globally"
	private String transformInvPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und invariantPattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		
		this.setFormulaInLTL("G(!(("+p+") & !("+s+")))");
		this.setFormulaInCTL("AG(("+p+")->("+s+") )");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformInvPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und invariantPattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		
		this.setFormulaInLTL("F("+r+")->(!(("+p+") & !("+s+"))U ("+r+"))");
		this.setFormulaInCTL("!E(!(("+r+")) U (!(((("+p+")->("+s+") ) | AG(!("+r+") ))) & !(("+r+"))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformInvPat_After(PL_initiatedPattern req){
		//bei AfterQScope und invariantPattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> ("+s+")))");
		this.setFormulaInCTL("AG(("+q+")->AG(("+p+")->("+s+") ))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformInvPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und invariantPattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+"))->((("+p+")->("+s+"))U "+r+"))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!(((("+p+")->("+s+") ) | AG(!("+r+") ))) & !(("+r+"))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformInvPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		p = this.toSMVString(p);
		s = this.toSMVString(s);
		r = this.toSMVString(r);
		q = this.toSMVString(q);
		
		this.setFormulaInLTL("G((("+q+") & !("+r+"))->((G(("+p+")->("+s+"))) | ((("+p+")->("+s+")) U ("+r+"))))");
		this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!((("+p+")->("+s+") )) & !(("+r+"))))))");			
		this.setFormulaInTCTL(this.getFormulaInCTL());
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//BoundedExistence PATTERN
	protected String transformbndExistencePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformbndExisPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformbndExisPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformbndExisPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformbndExisPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformbndExisPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to BoundedExistencePattern";
	}
	//Scope "Globally"
	private String transformbndExisPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und bndExistencePattern
		String p = req.getFirstNonLiteralTerminal();
		this.setFormulaInLTL("G(!("+p+") | ("+p+") U (G("+p+") | ("+p+") U ((G !("+p+")) | !("+p+") U (G ("+p+") | ("+p+") U (G !("+p+"))))))");
		this.setFormulaInCTL("!EF(!("+p+") & EX(("+p+") & EF(!("+p+") & EX(("+p+") & EF(!("+p+") & EX(("+p+") ))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformbndExisPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und bndExistencePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		
		this.setFormulaInLTL("!("+r+")->((!("+p+") & !("+r+")) | (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | ((!("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | ((!("+p+") U ("+r+")))))))))))");
		this.setFormulaInCTL("!E(!("+r+") U (!("+p+") &!("+r+") & EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") & EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") & EX(("+p+") &!("+r+") )))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformbndExisPat_After(PL_initiatedPattern req){
		//bei AfterQScope und bndExistencePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+q+") -> (!("+q+") U (("+q+") & ((G !("+p+")) | !("+p+") U ((G("+p+")) | (("+p+") U((G !("+p+")) | (!("+p+") U ((G("+p+")) | ("+p+") U (G !("+p+"))))))))))");
		this.setFormulaInCTL("!E(!("+q+") U (("+q+") & EF(!("+p+") & EX(("+p+") & EF (!("+p+") & EX(("+p+") & EF(!("+p+") & EX(("+p+") ))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformbndExisPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und bndExistencePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & F("+r+"))->((!("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | (( !("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | ((!("+p+") U ("+r+"))))))))))))");
		this.setFormulaInCTL("AG(("+q+") -> !E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") &!("+r+") &EF(("+r+") )))))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformbndExisPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G("+q+")->((!("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | (( !("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | (G(!("+p+")) | ("+p+") U ("+r+")) | G ("+p+")))))))))");
		this.setFormulaInCTL("AG(("+q+") -> !E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") &!("+r+") ))))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}

	//*********************************************************************************************
	//PRECEDENCE CHAIN PATTERN 2-1
	protected String transformPrecedenceChain21Pattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformPrecChain21Pat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformPrecChain21Pat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformPrecChain21Pat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformPrecChain21Pat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformPrecChain21Pat_After(req);
		}
		else return "unknown scope --- cannot be transformed to PrecedenceChain21Pattern";
	}
	//Scope "Globally"
	private String transformPrecChain21Pat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und bndExistencePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+p+") -> (!("+p+") U (("+s+") & !("+p+") & X(!("+p+") U ("+t+"))))");
		this.setFormulaInCTL("!E(!("+s+") U ("+p+") )&!E(!("+p+") U (("+s+") &!("+p+") &EX(E(!("+t+") U (("+p+") &!("+t+") )))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformPrecChain21Pat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und bndExistencePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> (!("+p+") U (("+r+") |(("+s+") & !("+p+") & X(!("+p+") U ("+t+")))))");
		this.setFormulaInCTL("!E((!("+s+") &!("+r+") ) U (("+p+") &!("+r+") ))&!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E((!("+t+") &!("+r+") ) U (("+p+") &!("+t+") &!("+r+") )))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformPrecChain21Pat_After(PL_initiatedPattern req){
		//bei AfterQScope und bndExistencePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("(G!("+q+")) | (!("+q+") U (("+q+") & F("+p+") -> (!("+p+") U (("+s+") & !("+p+") & X(!("+p+") U ("+t+"))))))");
		this.setFormulaInCTL("!E(!("+q+") U (("+q+") &E(!("+s+") U ("+p+") )&E(!("+p+") U (("+s+") &!("+p+") &EX(E(!("+t+") U (("+p+") &!("+t+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformPrecChain21Pat_Between(PL_initiatedPattern req){
		//bei BetweenScope und bndExistencePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (!("+p+") U (("+r+") |(("+s+") & !("+p+") & X(!("+p+") U ("+t+"))))))");
		this.setFormulaInCTL("AG(("+q+")-> !E((!("+s+") &!("+r+") ) U (("+p+") &!("+r+") &EF(("+r+") )))&!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E((!("+t+") &!("+r+") ) U (("+p+") &!("+t+") &!("+r+") &EF(("+r+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformPrecChain21Pat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> (F ("+p+") -> (!("+p+") U (("+r+") |(("+s+") & !("+p+") & X(!("+p+") U ("+t+")))))))");
		this.setFormulaInCTL("AG(("+q+")-> !E((!("+s+") &!("+r+") ) U (("+p+") &!("+r+") )) &!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") & EX(E((!("+t+") &!("+r+") ) U (("+p+") &!("+t+") &!("+r+") ))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//PRECEDENCE CHAIN PATTERN 1-2
	protected String transformPrecedenceChain12Pattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformPrecChain12Pat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformPrecChain12Pat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformPrecChain12Pat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformPrecChain12Pat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformPrecChain12Pat_After(req);
		}
		else return "unknown scope --- cannot be transformed to PrecedenceChain12Pattern";
	}
	//Scope "Globally"
	private String transformPrecChain12Pat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und PrecedenceChain12Pattern
		String s = req.getFirstNonLiteralTerminal();
		String t = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("(F("+s+") & XF("+t+")) -> (!("+s+") U ("+p+"))");
		this.setFormulaInCTL("!E(!("+p+") U (("+s+") &!("+p+") &EX(EF(("+t+") ))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformPrecChain12Pat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und PrecedenceChain12Pattern
		String r = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		String p = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> ((!(("+s+") & !("+r+") & X(!("+r+") U (("+t+") & !("+r+"))))) U (("+r+") | ("+p+")))");
		this.setFormulaInCTL("!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E(!("+r+") U (("+t+") &!("+r+") )))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformPrecChain12Pat_After(PL_initiatedPattern req){
		//bei AfterQScope und PrecedenceChain12Pattern
		String q = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		String p = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("(G!("+q+")) | (!("+q+") U (("+q+") & ((F(("+s+") & XF("+t+"))) -> (!("+s+") U ("+p+")))))");
		this.setFormulaInCTL("!E(!("+q+") U (("+q+") &E(!("+p+") U (("+s+") &!("+p+") &EX(EF(("+t+") ))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformPrecChain12Pat_Between(PL_initiatedPattern req){
		//bei BetweenScope und PrecedenceChain12Pattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		String p = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & F("+r+")) -> ((!(("+s+") & !("+r+") & X(!("+r+") U (("+t+") & !("+r+"))))) U (("+r+")|("+p+"))))");
		this.setFormulaInCTL("AG(("+q+")-> !E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E(!("+r+") U (("+t+") &!("+r+") &EF(("+r+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformPrecChain12Pat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		String p = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> (!(("+s+") & !("+r+") & X(!("+r+") U (("+t+") & !("+r+")))) U (("+r+") | ("+p+")) | G(!(("+s+")& XF("+t+")))))");
		this.setFormulaInCTL("AG(("+q+")-> !E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E(!("+r+") U (("+t+") &!("+r+") ))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}

	//*********************************************************************************************
	//RESPONSE CHAIN PATTERN 2-1
	protected String transformResponseChain21Pattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformRespChain21Pat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformRespChain21Pat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformRespChain21Pat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformRespChain21Pat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformRespChain21Pat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponseChain21Pattern";
	}
	//Scope "Globally"
	private String transformRespChain21Pat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und RespChain21Pattern
		String s = req.getFirstNonLiteralTerminal();
		String t = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+s+") & XF("+t+")) -> X(F(("+t+") & F("+p+"))))");
		this.setFormulaInCTL("!EF(("+s+") & EX(EF(("+t+") & EG(!("+p+") ))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformRespChain21Pat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und RespChain21Pattern
		String r = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		String p = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> (("+s+") & X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+") & F("+p+")))) U ("+r+")");
		this.setFormulaInCTL("!E(!("+r+") U (("+s+") &!("+r+") & EX(E(!("+r+") U (("+t+") &!("+r+") &E(!("+p+") U ("+r+") ))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformRespChain21Pat_After(PL_initiatedPattern req){
		//bei AfterQScope und RespChain21Pattern
		String q = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		String p = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("(G(("+q+") -> G(("+s+") & XF("+t+") -> X(!("+t+") U (("+t+") & F("+p+")))))");
		this.setFormulaInCTL("!E(!("+q+") U (("+q+") &EF(("+s+") & EX(EF(("+t+") & EG(!("+p+") ))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformRespChain21Pat_Between(PL_initiatedPattern req){
		//bei BetweenScope und RespChain21Pattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		String p = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (("+s+") & X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+") & F("+p+")))) U ("+r+"))");
		this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+s+") &!("+r+") & EX(E(!("+r+") U (("+t+") &!("+r+") &E(!("+p+") U ("+r+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformRespChain21Pat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		String p = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> (("+s+") & X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+") & F("+p+")))) U (("+r+") | G(("+s+")& X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+")& F("+p+"))))))");
		this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+s+") &!("+r+") & EX(E(!("+r+") U (("+t+") &!("+r+") & (E(!("+p+") U ("+r+") ) | EG(!("+p+") &!("+r+") ))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//RESPONSE CHAIN PATTERN 1-2
	protected String transformResponseChain12Pattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformRespChain12Pat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformRespChain12Pat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformRespChain12Pat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformRespChain12Pat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformRespChain12Pat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponseChain12Pattern";
	}
	//Scope "Globally"
	private String transformRespChain12Pat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und RespChain12Pattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+p+") -> F(("+s+") & XF("+t+")))");
		this.setFormulaInCTL("AG(("+p+") -> AF(("+s+") &AX(AF(("+t+") ))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformRespChain12Pat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und RespChain12Pattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & X(!("+r+") U ("+t+"))))) U ("+r+")");
		this.setFormulaInCTL("!E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & EX(E(!("+t+") U ("+r+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformRespChain12Pat_After(PL_initiatedPattern req){
		//bei AfterQScope und RespChain12Pattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> (("+s+") & XF("+t+"))))");
		this.setFormulaInCTL("!E(!("+q+") U (("+q+") &EF(("+p+") &(EG(!("+s+") ) | EF(("+s+") & EX(EG(!("+t+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformRespChain12Pat_Between(PL_initiatedPattern req){
		//bei BetweenScope und RespChain12Pattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & X(!("+r+") U ("+t+"))))) U ("+r+"))");
		this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & EX(E(!("+t+") U ("+r+") ))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformRespChain12Pat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & X(!("+r+") U ("+t+"))))) U (("+r+") | G(("+p+") -> (("+s+") & XF("+t+")))))");
		this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | EG(!("+s+") &!("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & EX(E(!("+t+") U ("+r+") ) | EG(!("+t+") &!("+r+") ))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//CONSTRAINED CHAIN PATTERN 
	protected String transformConstrainedChainPattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformConstrainedChainPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformConstrainedChainPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformConstrainedChainPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformConstrainedChainPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformConstrainedChainPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ConstrainedChainPattern";
	}
	//Scope "Globally"
	private String transformConstrainedChainPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und ConstrainedChainPattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String t = req.getThirdNonLiteralTerminal();
		String z = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+p+") -> F(("+s+") & !("+z+") & X(!("+z+") U ("+t+"))))");
		this.setFormulaInCTL("AG(("+p+") -> AF(("+s+") &!("+z+") &AX(A(!("+z+") U ("+t+") ))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformConstrainedChainPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und ConstrainedChainPattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		String z = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("F("+r+") -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & !("+z+") & X((!("+r+") & !("+z+")) U ("+t+"))))) U ("+r+")");
		this.setFormulaInCTL("!E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & (E(!("+t+") U ("+z+") )|EX(E(!("+t+") U ("+r+") ))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformConstrainedChainPat_After(PL_initiatedPattern req){
		//bei AfterQScope und ConstrainedChainPattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String t = req.getFourthNonLiteralTerminal();
		String z = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> (("+s+") & !("+z+") & X(!("+z+") U ("+t+")))))");
		this.setFormulaInCTL("!E(!("+q+") U (("+q+") &EF(("+p+") &EG(!("+s+") ) | EF(("+s+") &(E(!("+t+") U ("+z+") )|EX(EG(!("+t+") )))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformConstrainedChainPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und ConstrainedChainPattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		String z = req.getSixthNonLiteralTerminal();
		
		this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & !("+z+") & X((!("+r+") & !("+z+")) U ("+t+"))))) U ("+r+"))");
		this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & (E(!("+t+") U ("+z+") )|EX(E(!("+t+") U ("+r+") )))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformConstrainedChainPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		String z = req.getSixthNonLiteralTerminal();
		
		this.setFormulaInLTL("G(("+q+") -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & !("+z+") & X((!("+r+") & !("+z+")) U ("+t+"))))) U (("+r+") | G(("+p+") -> (("+s+") & !("+z+") & X(!("+z+") U ("+t+"))))))");
		this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") )| EG(!("+s+") &!("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & (E(!("+t+") U ("+z+") )|EX(E(!("+t+") U ("+r+") )| EG(!("+t+") &!("+r+") )))))))))");			
		this.setFormulaInTCTL("TBD");
		return this.getFormulaInLTL();
	}
	
	
	//*********************************************************************************************
	//POSSIBLE RESPONSE PATTERN  //Übersetzung nach CTL und TCTL möglich
	protected String transformPossibleResponsePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformPossibleResponsePat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformPossibleResponsePat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformPossibleResponsePat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformPossibleResponsePat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformPossibleResponsePat_After(req);
		}
		else return "unknown scope --- cannot be transformed to PossibleResponsePattern";
	}
	//Scope "Globally"
	private String transformPossibleResponsePat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und ConstrainedChainPattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		
		//in CTL: AG(("+p+") -> EF ("+s+") )
		this.setFormulaInCTL("AG(("+p+") -> EF ("+s+"))");
		this.setFormulaInTCTL("AG(("+p+") -> EF ("+s+"))");
		return this.getFormulaInLTL();
	}
	
	//Scope "Before R"
	private String transformPossibleResponsePat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und ConstrainedChainPattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("!E(!(("+r+")) U (!(((("+p+") -> E((!("+r+") ) U (("+s+") &!("+r+") ))) |AG(!("+r+") ))) & !(("+r+"))))");
		this.setFormulaInTCTL("!E(!(("+r+")) U (!(((("+p+") -> E((!("+r+") ) U (("+s+") &!("+r+") ))) |AG(!("+r+") ))) & !(("+r+"))))");
		
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q"
	private String transformPossibleResponsePat_After(PL_initiatedPattern req){
		//bei AfterQScope und ConstrainedChainPattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("!E(!((("+q+") & AG (("+p+") -> EF(("+s+") )))) U (!(!("+q+")) & !((("+q+") & AG (("+p+") -> EF(("+s+") ))))))");
		this.setFormulaInTCTL("!E(!((("+q+") & AG (("+p+") -> EF(("+s+") )))) U (!(!("+q+")) & !((("+q+") & AG (("+p+") -> EF(("+s+") ))))))");
		return this.getFormulaInLTL();
	}
	
	//Scope "Between Q and R"
	private String transformPossibleResponsePat_Between(PL_initiatedPattern req){
		//bei BetweenScope und ConstrainedChainPattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("AG(("+q+") &!("+r+") -> (!E(!(("+r+")) U (!(((("+p+") -> E(!("+r+") U (("+s+") &!("+r+") ))) | AG(!("+r+") ))) & !(("+r+"))))))");
		this.setFormulaInTCTL("AG(("+q+") &!("+r+") -> (!E(!(("+r+")) U (!(((("+p+") -> E(!("+r+") U (("+s+") &!("+r+") ))) | AG(!("+r+") ))) & !(("+r+"))))))");
		return this.getFormulaInLTL();
	}
	
	//Scope "After Q until R"
	private String transformPossibleResponsePat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String t = req.getFifthNonLiteralTerminal();
		String z = req.getSixthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("AG(("+q+") & !("+r+") -> (!E(!(("+r+")) U (!((("+p+") -> E(!("+r+") U (("+s+") & !("+r+") )))) & !(("+r+"))))))");
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E(!(("+r+")) U (!((("+p+") -> E(!("+r+") U (("+s+") & !("+r+") )))) & !(("+r+"))))))");
		return this.getFormulaInLTL();
	}
	
	//*********************************************************************************************
	//POSSIBLE BOUNDED RESPONSE PATTERN
	protected String transformPossBndResponsePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformPossBndRespPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformPossBndRespPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformPossBndRespPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformPossBndRespPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformPossBndRespPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponsePattern";
	}
	//Scope "Globally"
	private String transformPossBndRespPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+p+")-> EBF 0.."+c+" ("+s+") )");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformPossBndRespPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!(("+r+")) U (!(((("+p+") -> E[!("+r+") BU 0.."+c+"(("+s+") & !("+r+") )]) | AG(!("+r+") ))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformPossBndRespPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("!E[!((("+q+") & AG (("+p+") -> EBF 0.."+c+"(("+s+") )))) U (!(!("+q+") ) & !((("+q+") & AG (("+p+") -> EBF 0.."+c+"(("+s+") )))))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformPossBndRespPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!(("+r+")) U (!(((("+p+") -> E[!("+r+") BU 0.."+c+"(("+s+") & !("+r+") )]) | AG(!("+r+") ))) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformPossBndRespPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!(("+r+")) U (!((("+p+") -> E[!("+r+") BU 0.."+c+"(("+s+") & !("+r+") )])) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//*********************************************************************************************
	//POSSIBLE BOUNDED INVARIANCE PATTERN
	protected String transformPossBndInvariancePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformPossBndInvPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformPossBndInvPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformPossBndInvPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformPossBndInvPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformPossBndInvPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to bounded Invariance Pattern";
	}
	//Scope "Globally"
	private String transformPossBndInvPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+p+")-> EBG 0.."+c+" ("+s+") )");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformPossBndInvPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+") -> EBG 0.."+c+"(!("+r+") & ("+s+") ) | AG(!("+r+") ))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformPossBndInvPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("!E[!((("+q+") & AG (("+p+") -> EBG 0.."+c+"(("+s+") ))) U (!(!("+q+") ) & !((("+q+") & AG (("+p+") -> EBG 0.."+c+"(("+s+") ))))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformPossBndInvPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!("+r+") U (!((("+p+") -> EBG 0.."+c+"(("+s+") & !("+r+") )) | AG(!("+r+") )) & !("+r+"))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformPossBndInvPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!("+r+") U (!(("+p+") -> EBG 0.."+c+"(("+s+") & !("+r+") )) & !("+r+"))]))");
		return this.getFormulaInTCTL();
	}
	
	//*********************************************************************************************
	//BOUNDED INVARIANCE PATTERN
	protected String transformBndInvariancePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformBndInvPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformBndInvPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformBndInvPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformBndInvPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformBndInvPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to bounded Invariance Pattern";
	}
	//Scope "Globally"
	private String transformBndInvPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+p+")->ABG 0.."+c+"("+s+"))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformBndInvPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+")->ABG 0.."+c+"((("+s+") &!("+r+") )| AG(!("+r+") )))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformBndInvPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("AG(("+q+")-> AG(("+p+")->ABG 0.."+c+"("+s+")))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformBndInvPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!(("+r+")) U (!((("+p+")->ABG 0.."+c+"((("+s+") &!("+r+") )| AG(!("+r+") )))) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformBndInvPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!(("+r+")) U (!((("+p+")->ABG 0.."+c+"(("+s+") &!("+r+") ))) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//*********************************************************************************************
	//BOUNDED RESPONSE PATTERN
	protected String transformBndResponsePattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformBndRespPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformBndRespPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformBndRespPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformBndRespPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformBndRespPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponsePattern";
	}
	//Scope "Globally"
	private String transformBndRespPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String s = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+p+") -> ABF 0.."+c+"("+s+"))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformBndRespPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+") -> (A[!("+r+") BU 0.."+c+"(("+s+") &!("+r+") )] | AG(!("+r+") )))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformBndRespPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String s = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		q= this.toSMVString(q);	
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("AG(("+q+")->AG(("+p+") -> ABF 0.."+c+"(("+s+") )))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformBndRespPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q.toString()+") &!("+r.toString()+") )-> (!E[!(("+r.toString()+")) U (!(((("+p.toString()+") -> (A[!("+r.toString()+") BU 0.."+c+"(("+s.toString()+") &!("+r.toString()+") )])) | AG(!("+r.toString()+") ))) & !(("+r.toString()+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformBndRespPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String s = req.getFourthNonLiteralTerminal();
		String c = req.getFifthNonLiteralTerminal();
		
		p= this.toSMVString(p);
		s = this.toSMVString(s);
		r= this.toSMVString(r);
		q= this.toSMVString(q);
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q.toString()+") &!("+r.toString()+") )-> (!E[!(("+r.toString()+")) U (!((("+p.toString()+") -> A[!("+r.toString()+") BU 0.."+c+"(("+s.toString()+") &!("+r.toString()+") )])) & !(("+r.toString()+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//*********************************************************************************************
	//BOUNDED RECCURRENCE PATTERN
	protected String transformBndReccurrPattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformBndReccurrPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformBndReccurrPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformBndReccurrPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformBndReccurrPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformBndReccurrPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponsePattern";
	}
	//Scope "Globally"
	private String transformBndReccurrPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String c = req.getSecondNonLiteralTerminal();
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(ABF 0.."+c+"("+p+"))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformBndReccurrPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!(("+r+")) U (!((ABF 0.."+c+"(("+p+") |("+r+") | AG(!("+r+") )))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformBndReccurrPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("AG(("+q+")-> AG(ABF 0.."+c+"(("+p+") )))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformBndReccurrPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((ABF 0.."+c+"(("+p+") |("+r+") | AG(!("+r+") )))) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformBndReccurrPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!(ABF 0.."+c+"(("+p+") |("+r+") )) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//*********************************************************************************************
	//BOUNDED MINIMUM DURATION PATTERN
	protected String transformMinDurPattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformMinDurPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformMinDurPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformMinDurPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformMinDurPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformMinDurPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponsePattern";
	}
	//Scope "Globally"
	private String transformMinDurPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String c = req.getSecondNonLiteralTerminal();
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+p+") | !E[!(ABG 0.."+c+"(("+p+") )) U (!(!("+p+")) & !(ABG 0.."+c+"(("+p+") )))])");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformMinDurPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+") | !E[!((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )) U (!(!("+p+")) & !((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )))]| AG(!("+r+") ))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformMinDurPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("AG(("+q+") -> AG(("+p+") |!E[!(ABG 0.."+c+"(("+p+") )) U (!(!("+p+")) & !(ABG 0.."+c+"(("+p+") )))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformMinDurPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") | !E[!((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )) U (!(!("+p+")) & !((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )))] | AG(!("+r+") ))) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformMinDurPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") |!E[!((ABG 0.."+c+"(("+p+") &!("+r+") ))) U (!(!("+p+")) & !((ABG 0.."+c+"(("+p+") &!("+r+") ))))] | ("+r+") )) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//*********************************************************************************************
	//BOUNDED MAXIMUM DURATION PATTERN
	protected String transformMaxDurPattern(PL_initiatedPattern req){		
		String scope = req.getScope();

		if (scope.contains("Globally")){
			return this.transformMaxDurPat_Glob(req);
		}
		else if (scope.contains("Before")){
			return this.transformMaxDurPat_Before(req);
		}
		else if (scope.contains("Between")){
			return this.transformMaxDurPat_Between(req);
		}
		else if (scope.contains("until")){
			return this.transformMaxDurPat_Until(req);			
		}
		else if (scope.contains("After")){
			return this.transformMaxDurPat_After(req);
		}
		else return "unknown scope --- cannot be transformed to ResponsePattern";
	}
	//Scope "Globally"
	private String transformMaxDurPat_Glob(PL_initiatedPattern req){
		//bei GloballyScope und responsePattern
		String p = req.getFirstNonLiteralTerminal();
		String c = req.getSecondNonLiteralTerminal();
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG(("+p+") | !E[!((("+p+")& ABF 0.."+c+"(!("+p+") ))) U (!(!("+p+")) & !((("+p+")& ABF 0.."+c+"(!("+p+") ))))])");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Before R"
	private String transformMaxDurPat_Before(PL_initiatedPattern req){
		//bei BeforeRScope und responsePattern
		String r = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");	
		this.setFormulaInTCTL("!E[!("+r+") U (!((("+p+") | !E[!(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))) U (!(!("+p+")) & !(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))))] | AG(!("+r+") ))) & !(("+r+")))]");
		//this.setFormulaInTCTL("!E[!("+r+") U (!((("+p+") | !E[!((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) U (!(!("+p+")) & !(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") )))))]|("+r+") |AG(!("+r+") ))) | AG(!("+r+") ))) & !(("+r+")))]");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q"
	private String transformMaxDurPat_After(PL_initiatedPattern req){
		//bei AfterQScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String p = req.getSecondNonLiteralTerminal();
		String c = req.getThirdNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");		
		this.setFormulaInTCTL("AG(("+q+")->AG(("+p+") |!E[!((("+p+")& ABF 0.."+c+"(!("+p+") ))) U (!(!("+p+")) & !((("+p+")& ABF 0.."+c+"(!("+p+") ))))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "Between Q and R"
	private String transformMaxDurPat_Between(PL_initiatedPattern req){
		//bei BetweenScope und responsePattern
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") | !E[!(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))) U (!(!("+p+")) & !(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))))] | AG(!("+r+") ))) & !(("+r+")))]))");
		return this.getFormulaInTCTL();
	}
	
	//Scope "After Q until R"
	private String transformMaxDurPat_Until(PL_initiatedPattern req){
		String q = req.getFirstNonLiteralTerminal();
		String r = req.getSecondNonLiteralTerminal();
		String p = req.getThirdNonLiteralTerminal();
		String c = req.getFourthNonLiteralTerminal();
		
		this.setFormulaInLTL("n.a.");
		this.setFormulaInCTL("n.a.");			
		this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> !E[!(("+r+")) U (!((("+p+") | !E[!((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") )) |("+r+") ) U (!(!("+p+")) & !((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") )) |("+r+") ))])) & !(("+r+")))] )");
		return this.getFormulaInTCTL();
	}
	
	private String toSMVString(String p){
		p=p.replace('\u2227', '&');
		p=p.replace('\u2228', '|');
		return p;
	}
	
}
