package PatternLanguage;

import java.util.Vector;
import java.util.regex.Pattern;

/**
 * The class <code>PL_PatternList</code> aggregates all supported patterns, the requirements might be formalized in
 * 
 * 
 *
 * @author Amalinda Oertel
 * April 2010
 * 
 * 
 * @see PL_initiatedPattern
 */

public class PL_PatternList {
	private Vector<PL_Pattern> patternList;
	//QualitativePatterns
	private PL_Pattern absentPattern;
	private PL_Pattern universalityPattern;
	private PL_Pattern existencePattern;
	private PL_Pattern bndExistencePattern;
	private PL_Pattern precedencePattern;
	private PL_Pattern precedenceChainPattern12;
	private PL_Pattern precedenceChainPattern21;
	private PL_Pattern responsePattern;
	private PL_Pattern responseChainPattern12;
	private PL_Pattern responseChainPattern21;
	private PL_Pattern constrainedChainPattern12;
	//QuantitativePatterns
	private PL_Pattern minDurationPattern;
	private PL_Pattern maxDurationPattern;
	private PL_Pattern boundedRecurrencePattern;
	private PL_Pattern boundedResponsePattern;
	private PL_Pattern boundedInvariancePattern;
	//PossibilityPatterns
	private PL_Pattern possibilityPattern;
	private PL_Pattern possBndResponsePattern;
	private PL_Pattern possBndInvariancePattern;
	//InvariancePattern
	private PL_Pattern invariancePattern;
	
	
	
	
	//Constructors
	public PL_PatternList(){
		this.instantiatePatterns();
		this.patternList = new Vector<PL_Pattern>();	
		this.fillWithPatterns();
	}
	
	
	//Getter
	public Vector<PL_Pattern> getPatternList() {
		return patternList;
	}

	public PL_Pattern getAbsentPattern() {
		return absentPattern;
	}

	public PL_Pattern getUniversalityPattern() {
		return universalityPattern;
	}

	public PL_Pattern getExistencePattern() {
		return existencePattern;
	}

	public PL_Pattern getBndExistencePattern() {
		return bndExistencePattern;
	}

	public PL_Pattern getPrecedencePattern() {
		return precedencePattern;
	}

	public PL_Pattern getPrecedenceChainPattern12() {
		return precedenceChainPattern12;
	}

	public PL_Pattern getPrecedenceChainPattern21() {
		return precedenceChainPattern21;
	}

	public PL_Pattern getResponsePattern() {
		return responsePattern;
	}

	public PL_Pattern getResponseChainPattern12() {
		return responseChainPattern12;
	}

	public PL_Pattern getResponseChainPattern21() {
		return responseChainPattern21;
	}

	public PL_Pattern getConstrainedChainPattern12() {
		return constrainedChainPattern12;
	}

	public PL_Pattern getMinDurationPattern() {
		return minDurationPattern;
	}

	public PL_Pattern getMaxDurationPattern() {
		return maxDurationPattern;
	}

	public PL_Pattern getBoundedRecurrencePattern() {
		return boundedRecurrencePattern;
	}

	public PL_Pattern getBoundedResponsePattern() {
		return boundedResponsePattern;
	}

	public PL_Pattern getBoundedInvariancePattern() {
		return boundedInvariancePattern;
	}

	public PL_Pattern getPossibilityPattern() {
		return possibilityPattern;
	}

	public PL_Pattern getPossBndResponsePattern() {
		return possBndResponsePattern;
	}

	public PL_Pattern getPossBndInvariancePattern() {
		return possBndInvariancePattern;
	}

	public PL_Pattern getInvariancePattern() {
		return invariancePattern;
	}

	//InstantiatePatterns für den Konstruktor
	private void instantiatePatterns(){
		//instantiate qualitative patterns
		this.absentPattern = this.instantiateAbsentPattern();
		this.universalityPattern = this.instantiateUniversalityPattern();
		this.existencePattern = this.instantiateExistencePattern();
		this.bndExistencePattern = this.instantiateBndExistencePattern();
		this.precedencePattern = this.instantiatePrecedencePattern();
		this.precedenceChainPattern12 = this.instantiatePrecedenceChainPattern12();
		this.precedenceChainPattern21 = this.instantiatePrecedenceChainPattern21();
		this.responsePattern = this.instantiateResponsePattern();
		this.responseChainPattern12 = this.instantiateResponseChainPattern12();
		this.responseChainPattern21 = this.instantiateResponseChainPattern21();
		this.constrainedChainPattern12 = this.instantiateConstrainedChainPattern();
		//instantiate quantitative patterns
		this.minDurationPattern = this.instantiateMinDurationPattern();
		this.maxDurationPattern = this.instantiateMaxDurationPattern();
		this.boundedRecurrencePattern = this.instantiateBoundedReccurrencePattern();
		this.boundedResponsePattern = this.instantiateBndResponsePattern();
		this.boundedInvariancePattern = this.instantiateBndInvariancePattern();
		//extendedPatterns
		this.possibilityPattern = this.instantiatePossibilityPattern();
		this.possBndResponsePattern = this.instantiateBndPossResponsePattern();
		this.possBndInvariancePattern = this.instantiateBndPossInvariancePattern();
		this.invariancePattern = this.instantiateInvariantPattern();
	}
	
	//fillWithPatterns für den Konstruktor: packt die ganzen Patterns in die Liste rein
	private void fillWithPatterns(){
		this.patternList.addElement(this.absentPattern);
		this.patternList.addElement(this.universalityPattern);
		this.patternList.addElement(this.existencePattern);
		this.patternList.addElement(this.bndExistencePattern);
		this.patternList.addElement(precedencePattern);
		this.patternList.addElement(this.precedenceChainPattern12);
		this.patternList.addElement(this.precedenceChainPattern21);
		this.patternList.addElement(this.responsePattern);
		this.patternList.addElement(this.responseChainPattern12);
		this.patternList.addElement(this.responseChainPattern21);
		this.patternList.addElement(this.minDurationPattern);
		this.patternList.addElement(this.maxDurationPattern);
		this.patternList.addElement(this.boundedRecurrencePattern);
		this.patternList.addElement(this.boundedResponsePattern);
		this.patternList.addElement(this.boundedInvariancePattern);
		this.patternList.addElement(this.possibilityPattern);
		this.patternList.addElement(this.possBndResponsePattern);
		this.patternList.addElement(this.possBndInvariancePattern);
		this.patternList.addElement(this.invariancePattern);
	}
	
	//Zunächst die einzelnen Patterns
	//***********************************************************************
	//Qualitative Patterns
		private PL_Pattern instantiateAbsentPattern(){
			//PL_Pattern absentPattern = new PL_Pattern("absentPattern");
			PL_Pattern absentPattern = new PL_Pattern("absentPattern");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is never the case that \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is never the case that \"(.)*\" holds");
			absentPattern.setPattern(p);
			return absentPattern;
		}
		
		private PL_Pattern instantiateUniversalityPattern(){
			PL_Pattern universalityPattern = new PL_Pattern("universalityPattern");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is always the case that \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that \"(.)*\" holds");
			universalityPattern.setPattern(p);
			return universalityPattern;
		}
		
		private PL_Pattern instantiateExistencePattern(){
			PL_Pattern existencePattern = new PL_Pattern("existencePattern");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" eventually holds");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), \"(.)*\" eventually holds");
			existencePattern.setPattern(p);
			return existencePattern;
		}
		
		private PL_Pattern instantiateBndExistencePattern(){
			PL_Pattern bndExistencePattern = new PL_Pattern("boundedExistencePattern");
			//Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), transitions to states in which \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds occur at most twice");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), transitions to states in which \"(.)*\" holds occur at most twice");
			bndExistencePattern.setPattern(p);
			return bndExistencePattern;
		}
		
		private PL_Pattern instantiatePrecedencePattern(){
			PL_Pattern precedencePattern = new PL_Pattern("precedencePattern");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is always the case that if \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds, then \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" previously held");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" previously held");
			precedencePattern.setPattern(p);
			return precedencePattern;
		}
		
		private PL_Pattern instantiatePrecedenceChainPattern12(){
			PL_Pattern precedencePattern12 = new PL_Pattern("precedenceChainPattern12");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is always the case that if \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds and is succeeded by \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\", then \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" previously held");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds and is succeeded by \"(.)*\", then \"(.)*\" previously held");
			precedencePattern12.setPattern(p);
			return precedencePattern12;
		}
		
		private PL_Pattern instantiatePrecedenceChainPattern21(){
			PL_Pattern precedencePattern21 = new PL_Pattern("precedenceChainPattern21");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is always the case that if \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds, then \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" previously held and was preceded by \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\"");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" previously held and was preceded by \"(.)*\"");
			precedencePattern21.setPattern(p);
			return precedencePattern21;
		}
		
		private PL_Pattern instantiateResponsePattern(){
			PL_Pattern responsePattern = new PL_Pattern("responsePattern");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is always the case that if \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds, then \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" eventually holds");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" eventually holds");
			responsePattern.setPattern(p);
			return responsePattern;
		}
		
		private PL_Pattern instantiateResponseChainPattern12(){
			PL_Pattern responsePattern12 = new PL_Pattern("responseChainPattern12");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" eventually holds and is succeeded by \"(.)*\"");
			responsePattern12.setPattern(p);
			return responsePattern12;
		}
		
		private PL_Pattern instantiateResponseChainPattern21(){
			PL_Pattern responsePattern21 = new PL_Pattern("responseChainPattern21");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds and is succeeded by \"(.)*\", then \"(.)*\" eventually holds after \"(.)*\"")  ;
			responsePattern21.setPattern(p);
			return responsePattern21;
		}
		
		private PL_Pattern instantiateConstrainedChainPattern(){
			PL_Pattern constrainedPattern = new PL_Pattern("constrainedChainPattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" eventually holds and is succeeded by \"(.)*\", where \"(.)*\" does not hold between \"(.)*\" and \"(.)*\"")  ;
			constrainedPattern.setPattern(p);
			return constrainedPattern;
		}
		
		//Quantitative Patterns
		private PL_Pattern instantiateMinDurationPattern(){
			PL_Pattern minDurationPattern = new PL_Pattern("minDurationPattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that once \"(.)*\" becomes satisfied, it holds for at least \"[1-9]+[0-9]*\" time units");
			minDurationPattern.setPattern(p);
			return minDurationPattern;
		}
		
		private PL_Pattern instantiateMaxDurationPattern(){
			PL_Pattern maxDurationPattern = new PL_Pattern("maxDurationPattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that once \"(.)*\" becomes satisfied, it holds for less than \"[1-9]+[0-9]*\" time units");
			maxDurationPattern.setPattern(p);
			return maxDurationPattern;
		}
		
		private PL_Pattern instantiateBoundedReccurrencePattern(){
			PL_Pattern bndReccurrencePattern = new PL_Pattern("bndReccurrencePattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that \"(.)*\" holds at least every \"[1-9]+[0-9]*\" time units");
			bndReccurrencePattern.setPattern(p);
			return bndReccurrencePattern;
		}
		private PL_Pattern instantiateBndResponsePattern(){
			PL_Pattern bndResponsePattern = new PL_Pattern("bndResponsePattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" holds after at most \"[1-9]+[0-9]*\" time units");
			bndResponsePattern.setPattern(p);
			return bndResponsePattern;
		}
		private PL_Pattern instantiateBndInvariancePattern(){
			PL_Pattern bndInvariancePattern = new PL_Pattern("bndInvariancePattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" holds for at least \"[1-9]+[0-9]*\" time units");
			bndInvariancePattern.setPattern(p);
			return bndInvariancePattern;
		}
		
		//ExtendedPatterns: Possibility Patterns + InvariancePattern
		private PL_Pattern instantiatePossibilityPattern(){
			PL_Pattern possibilityPattern = new PL_Pattern("possibilityPattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), if \"(.)*\" holds, then there is at least one execution sequence such that \"(.)*\" eventually holds");
			possibilityPattern.setPattern(p);
			return possibilityPattern;
		}
		private PL_Pattern instantiateBndPossResponsePattern(){
			PL_Pattern bndPossResponsePattern = new PL_Pattern("bndPossResponsePattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), if \"(.)*\" holds, then there is at least one execution sequence such that \"(.)*\" holds after at most \"[1-9]+[0-9]*\" time units");
			bndPossResponsePattern.setPattern(p);
			return bndPossResponsePattern;
		}
		private PL_Pattern instantiateBndPossInvariancePattern(){
			PL_Pattern bndPossInvariancePattern = new PL_Pattern("bndPossInvariancePattern");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), if \"(.)*\" holds, then there is at least one execution sequence such that \"(.)*\" holds for at least \"[1-9]+[0-9]*\" time units");
			bndPossInvariancePattern.setPattern(p);
			return bndPossInvariancePattern;
		}
		private PL_Pattern instantiateInvariantPattern(){
			PL_Pattern invariantPattern = new PL_Pattern("invariantPattern");
			//Pattern p = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is always the case that if \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds, then \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds as well");
			Pattern p = Pattern.compile("(Globally|Before \"(.)*\"|After \"(.)*\"|After \"(.)*\" until \"(.)*\"|Between \"(.)*\" and \"(.)*\"), it is always the case that if \"(.)*\" holds, then \"(.)*\" holds as well");
			invariantPattern.setPattern(p);
			return invariantPattern;
		}
		
		//**************************************************************************************************
		//Functions
		//Prüft für einen String sentence und ein PL_Pattern, ob der String dem Pattern entspricht
		public boolean matches(String sentence, PL_Pattern p){
			boolean match = p.matchesToPattern(sentence);
			return match;
		}
		
		// Splitted einen String sentence auf, so dass alle Teile, die durch Anführungszeichen abgetrennt sind, 
		// in einen neuen ArrayString gepackt werden		
		public void splitForTerminals(String sentence){
			// Create a pattern to match breaks
	        Pattern p = Pattern.compile("(\\s*\"|\"\\s*)+");
	        // Split input with the pattern
	        String[] result = 
	                 p.split(sentence);
	        for (int i=0; i<result.length; i++)
	            System.out.println(result[i]);
	    }
		
		// Splitted einen String sentence auf, so dass alle Teile, die durch Anführungszeichen abgetrennt sind, 
		// in einen neuen ArrayString gepackt werden, und liefert den zurück		
		public String[] getSplittedSentence(String sentence){
			// Create a pattern to match breaks
	        Pattern p = Pattern.compile("(\\s*\"|\"\\s*)+");
	        // Split input with the pattern
	        String[] result = 
	                 p.split(sentence);
	        return result;
	    }
		
		// Liefert einen ArrayString zurück, in den alle nonLiteralTerminals eingetragen sind,
		// die in einem String sentence auftauchen		
		public Vector<String> getNonLiteralTerminals(String sentence){
			//Arbeitsvariablen
			Vector<String> result = new Vector();
			// Create splitted Strings
			String[] s = this.getSplittedSentence(sentence);
			//We know from our patterns that the nonLiteralTerminals are always stored in the odd indices of the array
	        for (int i=1; i<s.length; i=i+2){
	        	//System.out.println("i ist:"+i+"und j ist: "+j);
	        	result.addElement(s[i]); 
	        }
	        return result;
	    }
		
		//Liefert als String den Scope zurück, der in einem String sentence verwendet wird
		public String getScope(String sentence){
			if (sentence.contains("Globally")){
				return "Globally";
			}
			else 
				if (sentence.contains("Before")){
				return "Before";
			}
				else
					if(sentence.contains("until")){
						return "After...until";
					}
					else 
						if(sentence.contains("After")){
							return "After";
						}
						else
							if(sentence.contains("Between")){
								return "Between...and";
							}
			return "Error:Scope not recognized";
		}
		
		//Sucht für alle Patterns in der PatternListe ob es ein Pattern gibt, welches den String sentence matcht
		public PL_Pattern findMatchingPattern(String sentence){
			PL_Pattern pattern = new PL_Pattern();
			for (int i=0; i<patternList.size(); i++){
				PL_Pattern p = patternList.elementAt(i);
				boolean match = this.matches(sentence, p);
				if (match == true){
					System.out.println("Pattern \""+ p.getPatternName()+"\" matches");
					return p;
				}
			}
			System.out.println("No pattern matches --> still \""+ pattern.getPatternName()+"\"");
			return pattern;			
		}
		
		//Prüfe, ob die Anzahl der nonLiteralTerminals dem Pattern und dem Scope entspricht
		//to be implemented
		private boolean rightNumberOfNonLiteralTerminals(){
			return true;
		}

}
