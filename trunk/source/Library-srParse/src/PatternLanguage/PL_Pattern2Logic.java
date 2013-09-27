package PatternLanguage;

import java.util.Vector;

import pea.BooleanDecision;
import pea.CDD;
import pea.PhaseEventAutomata;
import pea.reqCheck.PatternToPEA;

/**
 * The class <code>PL_Pattern2Logic</code> offers functionality to
 * convert requirements, that are formalized in Patterns provided by <code>PL_PatternList</code>, to their formalization in either
 * Linear Timed Logic "LTL"
 * Computational Tree Logic "CTL"
 * Timed Computational Tree Logic "TCTL"
 * Duration Calculus "DC"
 * 
 * The DC formulas are directly transformed to PhaseEventAutomata (see <code>PhaseEventAutomata</code>)
 * 
 * Precondition: a string with a requirement that shall be transformed, was formerly transformed into an "initiatedPattern", thus, 
 * a parser already checked for scope, pattern class and literals
 * 
 *
 * @author Amalinda Oertel
 * April 2010
 * 
 * @see pea.CDD
 * @see pea.PhaseEventAutomata
 * @see PL_PatternList
 * @see PL_initiatedPattern
 */

public class PL_Pattern2Logic {

	
		///In dieser Klasse werden die Patterns, die in PL_PatternList.java definiert sind, nach LTL, CTL und TCTL übersetzt
		//(je nachdem was möglich ist)
		// Da für jedes Pattern je nach Scope unterschiedlich transformiert werden muß, schaut die Klasse ziemlich scheußlich aus :(
		
		//Die Übersetzten Patterns in NuSMV Syntax werden in der Klasse ToNuSMV generiert;
		
		//Precondition: ein zu übersetzender String wurde zuvor in ein "initiatedPattern" umgewandelt, sprich
		// der String wurde nach Scope, Pattern und den nonLiteralTerminals aufgegliedert
		
		String formulaInLTL;
		String formulaInCTL;
		String formulaInTCTL;
		
		//für Duration Calculus sind hier ein paar Default cdds für die Aufrufe
		private CDD q_cdd_default = BooleanDecision.create("Q");
		private CDD r_cdd_default = BooleanDecision.create("R");
		
		
		//for duration calculus we use a transformator to transform a duration calculus formula to a pea
		private PhaseEventAutomata pea;//für DC
		private PatternToPEA peaTransformator;
		
		//Constructors
		public PL_Pattern2Logic(){
			this.formulaInLTL = "init";
			this.formulaInCTL = "init";
			this.formulaInTCTL = "init";
			//for DC
			this.peaTransformator = new PatternToPEA();
			
		}

		//Getter/Setter
		
		private CDD getDefaultQ_cdd() {
			return q_cdd_default;
		}

		private CDD getDefaultR_cdd() {
			return r_cdd_default;
		}

		
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

		
		public String getFormulaInLTL() {
			return formulaInLTL;
		}

		private void setFormulaInLTL(String formulaInLTL) {
			this.formulaInLTL = formulaInLTL;
		}
		
		//Functions
		public String transformPatternToLogic(PL_initiatedPattern req, String requestedLogic){
			
			PL_Pattern patternClass = req.getPatternClass();
			PL_PatternList patternList = new PL_PatternList();
			
			if (patternClass.getPatternName() == patternList.getAbsentPattern().getPatternName()){
				return this.transformAbsentPattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getUniversalityPattern().getPatternName()){
				return this.transformUniversalityPattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getExistencePattern().getPatternName()){
				return this.transformExistencePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getPrecedencePattern().getPatternName()){
				return this.transformPrecedencePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getResponsePattern().getPatternName()){
				return this.transformResponsePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getInvariancePattern().getPatternName()){
				return this.transformInvariantPattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getBndExistencePattern().getPatternName()){
				return this.transformbndExistencePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getPrecedenceChainPattern21().getPatternName()){
				return this.transformPrecedenceChain21Pattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getPrecedenceChainPattern12().getPatternName()){
				return this.transformPrecedenceChain12Pattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getConstrainedChainPattern12().getPatternName()){
				return this.transformConstrainedChainPattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getResponseChainPattern21().getPatternName()){
				return this.transformResponseChain21Pattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getResponseChainPattern12().getPatternName()){
				return this.transformResponseChain12Pattern(req, requestedLogic);
			}		
			else if (patternClass.getPatternName() == patternList.getPossibilityPattern().getPatternName()){
				return this.transformPossibleResponsePattern(req, requestedLogic);
			}
			//Start quantitative patterns
			else if (patternClass.getPatternName() == patternList.getPossBndResponsePattern().getPatternName()){
				return this.transformPossBndResponsePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getPossBndInvariancePattern().getPatternName()){
				return this.transformPossBndInvariancePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getBoundedInvariancePattern().getPatternName()){
				return this.transformBndInvariancePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getBoundedResponsePattern().getPatternName()){
				return this.transformBndResponsePattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getBoundedRecurrencePattern().getPatternName()){
				return this.transformBndReccurrPattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getMinDurationPattern().getPatternName()){
				return this.transformMinDurPattern(req, requestedLogic);
			}
			else if (patternClass.getPatternName() == patternList.getMaxDurationPattern().getPatternName()){
				return this.transformMaxDurPattern(req, requestedLogic);
			}
			
			else return "ERROR: Unknown pattern --> cannot be transformed to LTL";
		}
		
		
		//Zunächst pro Pattern
		private String transformAbsentPattern(PL_initiatedPattern req, String wantedLogic){
			
			String scope = req.getScope();
			Vector<String> nonLiteralTerminals = req.getNonLiteralTerminals();	
			Vector<CDD> nonLiteralTerminalsCDD = req.getNonLiteralTerminalsCDD();	
			
			
			//PL_Pattern patternClass = req.getPatternClass();		
			//hier kein Check ob das auch das richtige Pattern ist, sondern implizite Annahme, dass
			// das früher gecheckt wird
			
			
			
			//Case: GLOBALLY
			if (scope.contains("Globally")){
				if (nonLiteralTerminals.size() !=1){
					//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
					System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
				}
				String p = req.getFirstNonLiteralTerminal();
				CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
				CDD q_cdd = this.getDefaultQ_cdd();
				CDD r_cdd = this.getDefaultR_cdd();
				
				this.setFormulaInLTL("G(!("+p+"))");
				this.setFormulaInCTL("AG(!("+p+"))");			
				this.setFormulaInTCTL(this.getFormulaInCTL());
				
				pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope);
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
				CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
				CDD q_cdd = this.getDefaultQ_cdd();
				CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
				
				this.setFormulaInLTL("F("+r+")->((!("+p+")U "+r+"))");	
				this.setFormulaInCTL("!E(!(("+r+")) U (!((!("+p+") | AG(!("+r+") ))) & !(("+r+"))))");			
				this.setFormulaInTCTL(this.getFormulaInCTL());
				
				pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope);
				
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
					CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
					CDD q_cdd = req.getFirstNonLiteralTerminalCDD();
					CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
					
					//p W q = (G p) | (p U q)
					this.setFormulaInLTL("G(("+q+" & !("+r+"))->((G!("+p+")) | (!("+p+") U ("+r+"))))");	
					this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!(!("+p+")) & !(("+r+"))))))");			
					this.setFormulaInTCTL(this.getFormulaInCTL());
					pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope);
					
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
						CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
						CDD q_cdd = req.getFirstNonLiteralTerminalCDD();
						CDD r_cdd = this.getDefaultR_cdd();
						
						this.setFormulaInLTL("G("+q+" -> G((!("+p+"))))");
						this.setFormulaInCTL("AG(("+q+")->AG(!("+p+") ))");			
						this.setFormulaInTCTL(this.getFormulaInCTL());
						pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope);
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
							CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
							CDD q_cdd = req.getFirstNonLiteralTerminalCDD();
							CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
							
							this.setFormulaInLTL("G(("+q+" & !("+r+") & F("+r+"))->((!("+p+")U "+r+")))");
							this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!((!("+p+") | AG(!("+r+") ))) & !(("+r+"))))))");			
							this.setFormulaInTCTL(this.getFormulaInCTL());
							pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope);
							//return this.getFormulaInLTL();
						}
			else return ("cannot be transformed to AbsentPattern");
			
			return getLogicString(wantedLogic);
			
		}
			
		
		
		//UNIVERSALITY PATTERN
		protected String transformUniversalityPattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformUnivPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformUnivPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformUnivPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformUnivPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformUnivPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to UniversalityPattern";
		}
		//Scope "Globally"
		private String transformUnivPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und universalityPattern			
			String p = req.getFirstNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd();
			CDD r_cdd = this.getDefaultR_cdd();
			
			this.setFormulaInLTL("G("+p+")");
			this.setFormulaInCTL("AG(("+p+"))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope);
			
			return getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformUnivPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und universalityPattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("F("+r+")-> ("+p+" U "+r+")");
			this.setFormulaInCTL("!E(!(("+r+")) U (!((("+p+") |AG(!("+r+") ))) & !(("+r+"))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope);

			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformUnivPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und universalityPattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd(); 
			
			this.setFormulaInLTL("G(("+q+") -> G("+p+"))");
			this.setFormulaInCTL("AG(("+q+") -> AG(("+p+") ))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformUnivPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und universalityPattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+")) -> (("+p+") U ("+r+")))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!((("+p+") |AG(!("+r+") ))) & !(("+r+"))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformUnivPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (G("+p+") | (("+p+") U ("+r+"))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!(("+p+")) & !(("+r+"))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//EXISTENCE PATTERN
		protected String transformExistencePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformExisPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformExisPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformExisPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformExisPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformExisPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ExistencePattern";
		}
		//Scope "Globally"
		private String transformExisPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und existencePattern
			String p = req.getFirstNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); 
			CDD r_cdd = this.getDefaultR_cdd();
			
			this.setFormulaInLTL("F("+p+")");
			this.setFormulaInCTL("AF(("+p+") )");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.existencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformExisPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und existencePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); 
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G(!("+r+"))|(!("+r+") U ("+p+" & (!("+r+"))))");
			this.setFormulaInCTL("!E(!((("+p+") &!("+r+") )) U (!(!("+r+")) & !((("+p+") &!("+r+") ))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.existencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformExisPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und existencePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd();
			
			this.setFormulaInLTL("G(!("+q+") | F("+q+" & F("+p+")))");
			this.setFormulaInCTL("!E(!((("+q+") & AF(("+p+") ))) U (!(!("+q+")) & !((("+q+") & AF(("+p+") )))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.existencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformExisPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und existencePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (G(!("+r+"))|(!("+r+") U ("+p+" & (!("+r+"))))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") ) ->(!E(!((("+p+") &!("+r+") )) U (!(!("+r+")) & !((("+p+") &!("+r+") ))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.existencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformExisPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (!("+r+") U ("+p+" & (!("+r+")))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") ) -> A(!("+r+") U (("+p+") &!("+r+") )))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.existencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		
		//*********************************************************************************************
		//PRECEDENCE PATTERN
		protected String transformPrecedencePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformPrecPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformPrecPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformPrecPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformPrecPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformPrecPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to PrecedencePattern";
		}
		//Scope "Globally"
		private String transformPrecPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und precedencePattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); 
			CDD r_cdd = this.getDefaultR_cdd();
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("((G !("+p+"))|(!("+p+") U ("+s+")))");
			this.setFormulaInCTL("!E(!(("+s+")) U (!(!("+p+")) & !(("+s+"))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.precedencePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformPrecPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und precedencePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); 
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("F("+r+") -> (!("+p+") U (("+s+") | ("+r+")))");
			this.setFormulaInCTL("!E(!((("+s+") | ("+r+") )) U (!((!("+p+") |AG(!("+r+") ))) & !((("+s+") | ("+r+") ))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.precedencePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformPrecPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und precedencePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd();
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G(!("+q+")) | F("+q+" & ((G !("+p+"))|(!("+p+") U ("+s+"))))");
			this.setFormulaInCTL("!E(!((("+q+") & !E(!(("+s+")) U (!(!("+p+")) & !(("+s+")))))) U (!(!("+q+") ) & !((("+q+") & !E(!(("+s+")) U (!(!("+p+")) & !(("+s+"))))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.precedencePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformPrecPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und precedencePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+")) -> (!("+p+") U (("+s+") | ("+r+"))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!((("+s+") |("+r+") )) U (!((!("+p+") | AG(!("+r+") ))) & !((("+s+") |("+r+") ))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			this.pea = peaTransformator.precedencePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformPrecPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			
			this.pea = peaTransformator.precedencePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			this.setFormulaInLTL("G((("+q+") & !("+r+")) -> ((G !("+p+"))|(!("+p+") U (("+s+") | ("+r+")))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!((("+s+") |("+r+") )) U (!(!("+p+")) & !((("+s+") |("+r+") ))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			
			
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//RESPONSE PATTERN
		protected String transformResponsePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformRespPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformRespPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformRespPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformRespPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformRespPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponsePattern";
		}
		//Scope "Globally"
		private String transformRespPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und responsePattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			this.setFormulaInLTL("G(("+p+") -> F("+s+"))");
			this.setFormulaInCTL("AG(("+p+")-> AF(("+s+") ))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformRespPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und responsePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);			
			this.setFormulaInLTL("F("+r+") -> (("+p+") -> (!("+r+") U (("+s+") & (!("+r+")))))U("+r+")");
			this.setFormulaInCTL("!E(!(("+r+")) U (!(((("+p+") -> A(!("+r+") U (("+s+") &!("+r+") )))| AG(!("+r+") ))) & !(("+r+"))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformRespPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); //dummy für aufruf
			
			this.pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);			
			this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> F("+s+")))");
			this.setFormulaInCTL("!E(!((("+q+") &AG(("+p+")->AF(("+s+") )))) U (!(!("+q+") ) & !((("+q+") &AG(("+p+")->AF(("+s+") ))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformRespPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);
			
			this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+")) -> (("+p+") -> (!("+r+") U (("+s+") & (!("+r+"))))) U ("+r+"))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!(((("+p+")->A(!("+r+") U (("+s+") &!("+r+") ))) | AG(!("+r+") ))) & !(("+r+"))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformRespPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);			
			this.setFormulaInLTL("G((("+q+") & !("+r+")) -> (G(("+p+") -> (!("+r+") U (("+s+") & (!("+r+"))))) | ((("+p+") -> (!("+r+") U (("+s+") & (!("+r+"))))) U("+r+"))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )-> (!E(!(("+r+")) U (!((("+p+")->A(!("+r+") U (("+s+") &!("+r+") )))) & !(("+r+"))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//Invariant PATTERN
		protected String transformInvariantPattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformInvPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformInvPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformInvPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformInvPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformInvPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to InvariantPattern";
		}
		//Scope "Globally"
		private String transformInvPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und invariantPattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.invariantPattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);	
			this.setFormulaInLTL("G(!(("+p+") & !("+s+")))");
			this.setFormulaInCTL("AG(("+p+")->("+s+") )");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformInvPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und invariantPattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.invariantPattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);				
			this.setFormulaInLTL("F("+r+")->(!(("+p+") & !("+s+"))U ("+r+"))");
			this.setFormulaInCTL("!E(!(("+r+")) U (!(((("+p+")->("+s+") ) | AG(!("+r+") ))) & !(("+r+"))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformInvPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und invariantPattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.invariantPattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);	
			
			this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> ("+s+")))");
			this.setFormulaInCTL("AG(("+q+")->AG(("+p+")->("+s+") ))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformInvPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und invariantPattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.invariantPattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);				
			this.setFormulaInLTL("G((("+q+") & !("+r+") & F("+r+"))->((("+p+")->("+s+"))U "+r+"))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!(((("+p+")->("+s+") ) | AG(!("+r+") ))) & !(("+r+"))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformInvPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			
			this.pea = peaTransformator.invariantPattern(p_cdd, q_cdd, r_cdd, s_cdd, scope);				
			this.setFormulaInLTL("G((("+q+") & !("+r+"))->((G(("+p+")->("+s+"))) | ((("+p+")->("+s+")) U ("+r+"))))");
			this.setFormulaInCTL("AG((("+q+") &!("+r+") )->(!E(!(("+r+")) U (!((("+p+")->("+s+") )) & !(("+r+"))))))");			
			this.setFormulaInTCTL(this.getFormulaInCTL());
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//BoundedExistence PATTERN
		protected String transformbndExistencePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformbndExisPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformbndExisPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformbndExisPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformbndExisPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformbndExisPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to BoundedExistencePattern";
		}
		//Scope "Globally"
		private String transformbndExisPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und bndExistencePattern
			String p = req.getFirstNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf
			
			this.pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope);
			this.setFormulaInLTL("G(!("+p+") | ("+p+") U (G("+p+") | ("+p+") U ((G !("+p+")) | !("+p+") U (G ("+p+") | ("+p+") U (G !("+p+"))))))");
			this.setFormulaInCTL("!EF(!("+p+") & EX(("+p+") & EF(!("+p+") & EX(("+p+") & EF(!("+p+") & EX(("+p+") ))))))");			
			this.setFormulaInTCTL("TBD");
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformbndExisPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und bndExistencePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();
			
			this.setFormulaInLTL("!("+r+")->((!("+p+") & !("+r+")) | (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | ((!("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | ((!("+p+") U ("+r+")))))))))))");
			this.setFormulaInCTL("!E(!("+r+") U (!("+p+") &!("+r+") & EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") & EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") & EX(("+p+") &!("+r+") )))))))))");			
			this.setFormulaInTCTL("TBD");
			this.pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope);
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformbndExisPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und bndExistencePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf
			
			this.pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope);			
			this.setFormulaInLTL("F("+q+") -> (!("+q+") U (("+q+") & ((G !("+p+")) | !("+p+") U ((G("+p+")) | (("+p+") U((G !("+p+")) | (!("+p+") U ((G("+p+")) | ("+p+") U (G !("+p+"))))))))))");
			this.setFormulaInCTL("!E(!("+q+") U (("+q+") & EF(!("+p+") & EX(("+p+") & EF (!("+p+") & EX(("+p+") & EF(!("+p+") & EX(("+p+") ))))))))");			
			this.setFormulaInTCTL("TBD");
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformbndExisPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und bndExistencePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			this.setFormulaInLTL("G((("+q+") & F("+r+"))->((!("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | (( !("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | ((!("+p+") U ("+r+"))))))))))))");
			this.setFormulaInCTL("AG(("+q+") -> !E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") &!("+r+") &EF(("+r+") )))))))))))");			
			this.setFormulaInTCTL("TBD");
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformbndExisPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			
			this.pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope);
			
			this.setFormulaInLTL("G("+q+")->((!("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | (( !("+p+") & !("+r+")) U (("+r+") | ((("+p+") & !("+r+")) U (("+r+") | (G(!("+p+")) | ("+p+") U ("+r+")) | G ("+p+")))))))))");
			this.setFormulaInCTL("AG(("+q+") -> !E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") & E(!("+r+") U (!("+p+") &!("+r+") &EX(("+p+") &!("+r+") ))))))))))");			
			this.setFormulaInTCTL("TBD");
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			return getLogicString(requestedLogic);
		}

		//*********************************************************************************************
		//PRECEDENCE CHAIN PATTERN 2-1
		protected String transformPrecedenceChain21Pattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformPrecChain21Pat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformPrecChain21Pat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformPrecChain21Pat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformPrecChain21Pat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformPrecChain21Pat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to PrecedenceChain21Pattern";
		}
		//Scope "Globally"
		private String transformPrecChain21Pat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und bndExistencePattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String t = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD();
			CDD t_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);			
			this.setFormulaInLTL("F("+p+") -> (!("+p+") U (("+s+") & !("+p+") & X(!("+p+") U ("+t+"))))");
			this.setFormulaInCTL("!E(!("+s+") U ("+p+") )&!E(!("+p+") U (("+s+") &!("+p+") &EX(E(!("+t+") U (("+p+") &!("+t+") )))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformPrecChain21Pat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und bndExistencePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("F("+r+") -> (!("+p+") U (("+r+") |(("+s+") & !("+p+") & X(!("+p+") U ("+t+")))))");
			this.setFormulaInCTL("!E((!("+s+") &!("+r+") ) U (("+p+") &!("+r+") ))&!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E((!("+t+") &!("+r+") ) U (("+p+") &!("+t+") &!("+r+") )))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformPrecChain21Pat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und bndExistencePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("(G!("+q+")) | (!("+q+") U (("+q+") & F("+p+") -> (!("+p+") U (("+s+") & !("+p+") & X(!("+p+") U ("+t+"))))))");
			this.setFormulaInCTL("!E(!("+q+") U (("+q+") &E(!("+s+") U ("+p+") )&E(!("+p+") U (("+s+") &!("+p+") &EX(E(!("+t+") U (("+p+") &!("+t+") )))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformPrecChain21Pat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und bndExistencePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String t = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFifthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (!("+p+") U (("+r+") |(("+s+") & !("+p+") & X(!("+p+") U ("+t+"))))))");
			this.setFormulaInCTL("AG(("+q+")-> !E((!("+s+") &!("+r+") ) U (("+p+") &!("+r+") &EF(("+r+") )))&!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E((!("+t+") &!("+r+") ) U (("+p+") &!("+t+") &!("+r+") &EF(("+r+") )))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformPrecChain21Pat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String t = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFifthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("G(("+q+") -> (F ("+p+") -> (!("+p+") U (("+r+") |(("+s+") & !("+p+") & X(!("+p+") U ("+t+")))))))");
			this.setFormulaInCTL("AG(("+q+")-> !E((!("+s+") &!("+r+") ) U (("+p+") &!("+r+") )) &!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") & EX(E((!("+t+") &!("+r+") ) U (("+p+") &!("+t+") &!("+r+") ))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//PRECEDENCE CHAIN PATTERN 1-2
		protected String transformPrecedenceChain12Pattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformPrecChain12Pat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformPrecChain12Pat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformPrecChain12Pat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformPrecChain12Pat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformPrecChain12Pat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to PrecedenceChain12Pattern";
		}
		//Scope "Globally"
		private String transformPrecChain12Pat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und PrecedenceChain12Pattern
			String s = req.getFirstNonLiteralTerminal();
			String t = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getSecondNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("(F("+s+") & XF("+t+")) -> (!("+s+") U ("+p+"))");
			this.setFormulaInCTL("!E(!("+p+") U (("+s+") &!("+p+") &EX(EF(("+t+") ))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformPrecChain12Pat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und PrecedenceChain12Pattern
			String r = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String t = req.getThirdNonLiteralTerminal();
			String p = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getFourthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("F("+r+") -> ((!(("+s+") & !("+r+") & X(!("+r+") U (("+t+") & !("+r+"))))) U (("+r+") | ("+p+")))");
			this.setFormulaInCTL("!E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E(!("+r+") U (("+t+") &!("+r+") )))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformPrecChain12Pat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und PrecedenceChain12Pattern
			String q = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String t = req.getThirdNonLiteralTerminal();
			String p = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getFourthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); 
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("(G!("+q+")) | (!("+q+") U (("+q+") & ((F(("+s+") & XF("+t+"))) -> (!("+s+") U ("+p+")))))");
			this.setFormulaInCTL("!E(!("+q+") U (("+q+") &E(!("+p+") U (("+s+") &!("+p+") &EX(EF(("+t+") ))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformPrecChain12Pat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und PrecedenceChain12Pattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			String p = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getFifthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);			
			this.setFormulaInLTL("G((("+q+") & F("+r+")) -> ((!(("+s+") & !("+r+") & X(!("+r+") U (("+t+") & !("+r+"))))) U (("+r+")|("+p+"))))");
			this.setFormulaInCTL("AG(("+q+")-> !E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E(!("+r+") U (("+t+") &!("+r+") &EF(("+r+") )))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformPrecChain12Pat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			String p = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getFifthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.precedenceChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("G(("+q+") -> (!(("+s+") & !("+r+") & X(!("+r+") U (("+t+") & !("+r+")))) U (("+r+") | ("+p+")) | G(!(("+s+")& XF("+t+")))))");
			this.setFormulaInCTL("AG(("+q+")-> !E((!("+p+") &!("+r+") ) U (("+s+") &!("+p+") &!("+r+") &EX(E(!("+r+") U (("+t+") &!("+r+") ))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}

		//*********************************************************************************************
		//RESPONSE CHAIN PATTERN 2-1
		protected String transformResponseChain21Pattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformRespChain21Pat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformRespChain21Pat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformRespChain21Pat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformRespChain21Pat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformRespChain21Pat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponseChain21Pattern";
		}
		//Scope "Globally"
		private String transformRespChain21Pat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und RespChain21Pattern
			String s = req.getFirstNonLiteralTerminal();
			String t = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getSecondNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);			
			this.setFormulaInLTL("G((("+s+") & XF("+t+")) -> X(F(("+t+") & F("+p+"))))");
			this.setFormulaInCTL("!EF(("+s+") & EX(EF(("+t+") & EG(!("+p+") ))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformRespChain21Pat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und RespChain21Pattern
			String r = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String t = req.getThirdNonLiteralTerminal();
			String p = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getFourthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);			
			this.setFormulaInLTL("F("+r+") -> (("+s+") & X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+") & F("+p+")))) U ("+r+")");
			this.setFormulaInCTL("!E(!("+r+") U (("+s+") &!("+r+") & EX(E(!("+r+") U (("+t+") &!("+r+") &E(!("+p+") U ("+r+") ))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformRespChain21Pat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und RespChain21Pattern
			String q = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String t = req.getThirdNonLiteralTerminal();
			String p = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getFourthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); 
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("(G(("+q+") -> G(("+s+") & XF("+t+") -> X(!("+t+") U (("+t+") & F("+p+")))))");
			this.setFormulaInCTL("!E(!("+q+") U (("+q+") &EF(("+s+") & EX(EF(("+t+") & EG(!("+p+") ))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformRespChain21Pat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und RespChain21Pattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			String p = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getFifthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (("+s+") & X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+") & F("+p+")))) U ("+r+"))");
			this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+s+") &!("+r+") & EX(E(!("+r+") U (("+t+") &!("+r+") &E(!("+p+") U ("+r+") )))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformRespChain21Pat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			String p = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getFifthNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("G(("+q+") -> (("+s+") & X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+") & F("+p+")))) U (("+r+") | G(("+s+")& X(!("+r+") U ("+t+")) -> X(!("+r+") U (("+t+")& F("+p+"))))))");
			this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+s+") &!("+r+") & EX(E(!("+r+") U (("+t+") &!("+r+") & (E(!("+p+") U ("+r+") ) | EG(!("+p+") &!("+r+") ))))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//RESPONSE CHAIN PATTERN 1-2
		protected String transformResponseChain12Pattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformRespChain12Pat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformRespChain12Pat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformRespChain12Pat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformRespChain12Pat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformRespChain12Pat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponseChain12Pattern";
		}
		//Scope "Globally"
		private String transformRespChain12Pat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und RespChain12Pattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String t = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getThirdNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);			
			this.setFormulaInLTL("G(("+p+") -> F(("+s+") & XF("+t+")))");
			this.setFormulaInCTL("AG(("+p+") -> AF(("+s+") &AX(AF(("+t+") ))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformRespChain12Pat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und RespChain12Pattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);					
			this.setFormulaInLTL("F("+r+") -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & X(!("+r+") U ("+t+"))))) U ("+r+")");
			this.setFormulaInCTL("!E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & EX(E(!("+t+") U ("+r+") )))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformRespChain12Pat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und RespChain12Pattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String t = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd(); //dummy für aufruf
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFourthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);					
			this.setFormulaInLTL("G(("+q+") -> G(("+p+") -> (("+s+") & XF("+t+"))))");
			this.setFormulaInCTL("!E(!("+q+") U (("+q+") &EF(("+p+") &(EG(!("+s+") ) | EF(("+s+") & EX(EG(!("+t+") )))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformRespChain12Pat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und RespChain12Pattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String t = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFifthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);			
			this.setFormulaInLTL("G((("+q+") & F("+r+")) -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & X(!("+r+") U ("+t+"))))) U ("+r+"))");
			this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & EX(E(!("+t+") U ("+r+") ))))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformRespChain12Pat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String t = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD(); 
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD(); 
			CDD t_cdd = req.getFifthNonLiteralTerminalCDD(); 
			
			this.pea = peaTransformator.responseChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope);				
			this.setFormulaInLTL("G(("+q+") -> (("+p+") -> (!("+r+") U (("+s+") & !("+r+") & X(!("+r+") U ("+t+"))))) U (("+r+") | G(("+p+") -> (("+s+") & XF("+t+")))))");
			this.setFormulaInCTL("AG(("+q+")-> !E(!("+r+") U (("+p+") &!("+r+") &(E(!("+s+") U ("+r+") ) | EG(!("+s+") &!("+r+") ) | E(!("+r+") U(("+s+") &!("+r+") & EX(E(!("+t+") U ("+r+") ) | EG(!("+t+") &!("+r+") ))))))))");			
			this.setFormulaInTCTL("TBD");
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//CONSTRAINED CHAIN PATTERN 
		protected String transformConstrainedChainPattern(PL_initiatedPattern req,String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformConstrainedChainPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformConstrainedChainPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformConstrainedChainPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformConstrainedChainPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformConstrainedChainPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ConstrainedChainPattern";
		}
		//Scope "Globally"
		private String transformConstrainedChainPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformConstrainedChainPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformConstrainedChainPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformConstrainedChainPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformConstrainedChainPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
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
		protected String transformPossibleResponsePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformPossibleResponsePat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformPossibleResponsePat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformPossibleResponsePat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformPossibleResponsePat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformPossibleResponsePat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to PossibleResponsePattern";
		}
		//Scope "Globally"
		private String transformPossibleResponsePat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossibleResponsePat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossibleResponsePat_After(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossibleResponsePat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossibleResponsePat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
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
		protected String transformPossBndResponsePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformPossBndRespPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformPossBndRespPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformPossBndRespPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformPossBndRespPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformPossBndRespPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponsePattern";
		}
		//Scope "Globally"
		private String transformPossBndRespPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndRespPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndRespPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndRespPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndRespPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
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
		protected String transformPossBndInvariancePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformPossBndInvPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformPossBndInvPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformPossBndInvPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformPossBndInvPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformPossBndInvPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to bounded Invariance Pattern";
		}
		//Scope "Globally"
		private String transformPossBndInvPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndInvPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndInvPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndInvPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
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
		private String transformPossBndInvPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
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
		protected String transformBndInvariancePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformBndInvPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformBndInvPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformBndInvPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformBndInvPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformBndInvPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to bounded Invariance Pattern";
		}
		//Scope "Globally"
		private String transformBndInvPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und responsePattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();
			
			this.pea = peaTransformator.bndInvariancePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(("+p+")->ABG 0.."+c+"("+s+"))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformBndInvPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und responsePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den Aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndInvariancePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");	
			this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+")->ABG 0.."+c+"((("+s+") &!("+r+") )| AG(!("+r+") )))) & !(("+r+")))]");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformBndInvPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndInvariancePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");		
			this.setFormulaInTCTL("AG(("+q+")-> AG(("+p+")->ABG 0.."+c+"("+s+")))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformBndInvPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String c = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndInvariancePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!(("+r+")) U (!((("+p+")->ABG 0.."+c+"((("+s+") &!("+r+") )| AG(!("+r+") )))) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformBndInvPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String c = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();//dummy für den aufruf
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndInvariancePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(("+q+") & !("+r+") -> (!E[!(("+r+")) U (!((("+p+")->ABG 0.."+c+"(("+s+") &!("+r+") ))) & !(("+r+")))]))");
			
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//BOUNDED RESPONSE PATTERN
		protected String transformBndResponsePattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformBndRespPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformBndRespPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformBndRespPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformBndRespPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformBndRespPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponsePattern";
		}
		//Scope "Globally"
		private String transformBndRespPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und responsePattern
			String p = req.getFirstNonLiteralTerminal();
			String s = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf	
			CDD s_cdd = req.getSecondNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();
			
			this.pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(("+p+") -> ABF 0.."+c+"("+s+"))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformBndRespPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und responsePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();//dummy für den aufruf	
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");	
			this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+") -> (A[!("+r+") BU 0.."+c+"(("+s+") &!("+r+") )] | AG(!("+r+") )))) & !(("+r+")))]");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformBndRespPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String s = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf	
			CDD s_cdd = req.getThirdNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");		
			this.setFormulaInTCTL("AG(("+q+")->AG(("+p+") -> ABF 0.."+c+"(("+s+") )))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformBndRespPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String c = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();	
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!(((("+p+") -> (A[!("+r+") BU 0.."+c+"(("+s+") &!("+r+") )])) | AG(!("+r+") ))) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformBndRespPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String s = req.getFourthNonLiteralTerminal();
			String c = req.getFifthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();
			CDD s_cdd = req.getFourthNonLiteralTerminalCDD();
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") -> A[!("+r+") BU 0.."+c+"(("+s+") &!("+r+") )])) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//BOUNDED RECCURRENCE PATTERN
		protected String transformBndReccurrPattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformBndReccurrPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformBndReccurrPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformBndReccurrPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformBndReccurrPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformBndReccurrPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponsePattern";
		}
		//Scope "Globally"
		private String transformBndReccurrPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und responsePattern
			String p = req.getFirstNonLiteralTerminal();
			String c = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, c_int, scope);	
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(ABF 0.."+c+"("+p+"))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformBndReccurrPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und responsePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();		
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");	
			this.setFormulaInTCTL("!E[!(("+r+")) U (!((ABF 0.."+c+"(("+p+") |("+r+") | AG(!("+r+") )))) & !(("+r+")))]");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformBndReccurrPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");		
			this.setFormulaInTCTL("AG(("+q+")-> AG(ABF 0.."+c+"(("+p+") )))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformBndReccurrPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); //dummy für den aufruf
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((ABF 0.."+c+"(("+p+") |("+r+") | AG(!("+r+") )))) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformBndReccurrPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); //dummy für den aufruf
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!(ABF 0.."+c+"(("+p+") |("+r+") )) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//BOUNDED MINIMUM DURATION PATTERN
		protected String transformMinDurPattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformMinDurPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformMinDurPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformMinDurPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformMinDurPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformMinDurPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponsePattern";
		}
		//Scope "Globally"
		private String transformMinDurPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und responsePattern
			String p = req.getFirstNonLiteralTerminal();
			String c = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(("+p+") | !E[!(ABG 0.."+c+"(("+p+") )) U (!(!("+p+")) & !(ABG 0.."+c+"(("+p+") )))])");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformMinDurPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und responsePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();		
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);			
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");	
			this.setFormulaInTCTL("!E[!(("+r+")) U (!((("+p+") | !E[!((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )) U (!(!("+p+")) & !((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )))]| AG(!("+r+") ))) & !(("+r+")))]");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformMinDurPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);						
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");		
			this.setFormulaInTCTL("AG(("+q+") -> AG(("+p+") |!E[!(ABG 0.."+c+"(("+p+") )) U (!(!("+p+")) & !(ABG 0.."+c+"(("+p+") )))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformMinDurPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);					
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") | !E[!((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )) U (!(!("+p+")) & !((ABG 0.."+c+"((("+p+") &!("+r+") ) | AG(!("+r+") )) | ("+r+") )))] | AG(!("+r+") ))) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformMinDurPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") |!E[!((ABG 0.."+c+"(("+p+") &!("+r+") ))) U (!(!("+p+")) & !((ABG 0.."+c+"(("+p+") &!("+r+") ))))] | ("+r+") )) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//*********************************************************************************************
		//BOUNDED MAXIMUM DURATION PATTERN
		protected String transformMaxDurPattern(PL_initiatedPattern req, String requestedLogic){		
			String scope = req.getScope();

			if (scope.contains("Globally")){
				return this.transformMaxDurPat_Glob(req, requestedLogic, scope);
			}
			else if (scope.contains("Before")){
				return this.transformMaxDurPat_Before(req, requestedLogic, scope);
			}
			else if (scope.contains("Between")){
				return this.transformMaxDurPat_Between(req, requestedLogic, scope);
			}
			else if (scope.contains("until")){
				return this.transformMaxDurPat_Until(req, requestedLogic, scope);			
			}
			else if (scope.contains("After")){
				return this.transformMaxDurPat_After(req, requestedLogic, scope);
			}
			else return "unknown scope --- cannot be transformed to ResponsePattern";
		}
		//Scope "Globally"
		private String transformMaxDurPat_Glob(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei GloballyScope und responsePattern
			String p = req.getFirstNonLiteralTerminal();
			String c = req.getSecondNonLiteralTerminal();
			CDD p_cdd = req.getFirstNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);	
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG(("+p+") | !E[!((("+p+")& ABF 0.."+c+"(!("+p+") ))) U (!(!("+p+")) & !((("+p+")& ABF 0.."+c+"(!("+p+") ))))])");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Before R"
		private String transformMaxDurPat_Before(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BeforeRScope und responsePattern
			String r = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = this.getDefaultQ_cdd(); //dummy für den aufruf
			CDD r_cdd = req.getFirstNonLiteralTerminalCDD();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");	
			this.setFormulaInTCTL("!E[!("+r+") U (!((("+p+") | !E[!(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))) U (!(!("+p+")) & !(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))))] | AG(!("+r+") ))) & !(("+r+")))]");
			//this.setFormulaInTCTL("!E[!("+r+") U (!((("+p+") | !E[!((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) U (!(!("+p+")) & !(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") )))))]|("+r+") |AG(!("+r+") ))) | AG(!("+r+") ))) & !(("+r+")))]");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q"
		private String transformMaxDurPat_After(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei AfterQScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String p = req.getSecondNonLiteralTerminal();
			String c = req.getThirdNonLiteralTerminal();
			CDD p_cdd = req.getSecondNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); //dummy für den aufruf
			CDD r_cdd = this.getDefaultR_cdd();//dummy für den aufruf			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");		
			this.setFormulaInTCTL("AG(("+q+")->AG(("+p+") |!E[!((("+p+")& ABF 0.."+c+"(!("+p+") ))) U (!(!("+p+")) & !((("+p+")& ABF 0.."+c+"(!("+p+") ))))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "Between Q and R"
		private String transformMaxDurPat_Between(PL_initiatedPattern req, String requestedLogic, String scope){
			//bei BetweenScope und responsePattern
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);				
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> (!E[!(("+r+")) U (!((("+p+") | !E[!(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))) U (!(!("+p+")) & !(((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") |AG(!("+r+") ))) |("+r+") |AG(!("+r+") ))))] | AG(!("+r+") ))) & !(("+r+")))]))");
			return this.getLogicString(requestedLogic);
		}
		
		//Scope "After Q until R"
		private String transformMaxDurPat_Until(PL_initiatedPattern req, String requestedLogic, String scope){
			String q = req.getFirstNonLiteralTerminal();
			String r = req.getSecondNonLiteralTerminal();
			String p = req.getThirdNonLiteralTerminal();
			String c = req.getFourthNonLiteralTerminal();
			CDD p_cdd = req.getThirdNonLiteralTerminalCDD(); //für Duration Calculus muß das als CDD gegeben sein
			CDD q_cdd = req.getFirstNonLiteralTerminalCDD(); 
			CDD r_cdd = req.getSecondNonLiteralTerminalCDD();			
			int c_int = Integer.valueOf(c).intValue();;
			
			this.pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, c_int, scope);	
			
			this.setFormulaInLTL("n.a.");
			this.setFormulaInCTL("n.a.");			
			this.setFormulaInTCTL("AG((("+q+") &!("+r+") )-> !E[!(("+r+")) U (!((("+p+") | !E[!((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") )) |("+r+") ) U (!(!("+p+")) & !((("+p+")& ABF 0.."+c+"(!("+p+") |("+r+") )) |("+r+") ))])) & !(("+r+")))] )");
			return this.getLogicString(requestedLogic);
		}
		
		private String getLogicString(String requestedLogic){
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			if (requestedLogic.contains("LTL")){
				return this.getFormulaInLTL();
			}
			if (requestedLogic.contains("TCTL")){
				return this.getFormulaInTCTL();
			}
			else if (requestedLogic.contains("CTL")){
				return this.getFormulaInCTL();
			}
			if (requestedLogic.contains("DC")){
				//pea.dump();
				return "Pea dumped";
			}
			else 
				return "requested Logic unkown";
		}
		
		public PhaseEventAutomata getLogicPEA(String requestedLogic){
			//Abhängig der gewünschten Logic, gib requirement in entsprechender Logic zurück (für DC gib Pea zurück)
			if (requestedLogic.contains("LTL") || requestedLogic.contains("CTL")){ //String TCTL also contains "CTL"
				System.out.println("LTL, CTL, and TCTL cannot be transformed to PEA");
			}
			if (requestedLogic.contains("DC")){
				//pea.dump();
				return pea;
			}
			else {
				System.out.println("requested Logic "+ requestedLogic+ " unknown");
			}
			return pea;
		}
		
	}


