package PatternLanguage;

import java.util.regex.Pattern;

import java.util.Vector;

import framework.Term;


public class PL_Pattern {
	private String patternName;
	private Pattern pattern;
	private String patternAsString;
	
	//pro Scope und Pattern braucht man unterschiedlich viele nonLiteralTerminals;
	//private int numberNonLitTermGlobally;
	//private int numberNonLitTermBefore;
	//private int numberNonLitTermAfter;
	//private int numberNonLitTermUntil;
	//private int numberNonLitTermBetween;
		
	
	//Constructors
	public PL_Pattern(String name, Pattern pattern){
		this.patternName = name;
		this.pattern = pattern;	
		this.patternAsString = pattern.toString();
		
	}
	
	//Constructors
	public PL_Pattern(String name){
		this.patternName = name;
		this.pattern = Pattern.compile("init");
		this.patternAsString = pattern.toString();
		
	}
	
	//Constructors
	public PL_Pattern(String name, int globally, int before, int after, int between, int until){
		this.patternName = name;
		this.pattern = Pattern.compile("init");
		this.patternAsString = pattern.toString();
		
	}
	
	//Constructors
	public PL_Pattern(){
		this.patternName = "init";
		this.pattern = Pattern.compile("init");
		this.patternAsString = pattern.toString();
		
	}

//********************************************************************
//GET/SET PatternName
	public String getPatternName() {
		return patternName;
	}

	protected void setPatternName(String patternName) {
		this.patternName = patternName;
	}

//GET/SET pattern
	public Pattern getPattern() {
		return pattern;
	}
	protected void setPattern(Pattern pattern) {
		this.pattern = pattern;
		this.patternAsString = pattern.toString();
	}
	public String getPatternAsString() {
		return patternAsString;
	}

//***********************************************************************
	//Functions
	public boolean matchesToPattern(String sentence){
		boolean match = Pattern.matches(this.getPatternAsString(), sentence);
		return match;
	}
	
	
	}




